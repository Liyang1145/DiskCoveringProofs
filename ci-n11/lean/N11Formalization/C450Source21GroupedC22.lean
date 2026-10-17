import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC22
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((5:ℚ)/16),((3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/16),((3:ℚ)/8),((1463871339:ℚ)/2500000000),((6398344429:ℚ)/10000000000),((2071871339:ℚ)/5340000000),((25595033287:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((864045131:ℚ)/1250000000),((688904161751047546102843:ℚ)/14257800000000000000000000),((-610031791010128364860625439:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((1266734713:ℚ)/2000000000),((6637197269:ℚ)/10000000000),((1753134713:ℚ)/4424000000),((295635863:ℚ)/600000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1464011379:ℚ)/2500000000),((2442665887704775953328833244054964060583554241211233071:ℚ)/58977450000000000000000000000000000000000000000000000000),((-630754123663037489999552719:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((5:ℚ)/16),((3:ℚ)/8),((1643150463:ℚ)/2500000000),((1718989879:ℚ)/2500000000),((2251150463:ℚ)/5720000000),((6756969637:ℚ)/13825000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((263006237:ℚ)/500000000),((150309293565996560003350362387884028544826225116249360897:ℚ)/3711129590136718750000000000000000000000000000000000000000),((-39972174860154827321134839:ℚ)/115520000000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((1702858613:ℚ)/2500000000),((6995309471:ℚ)/10000000000),((2310858613:ℚ)/5815000000),((27385928413:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2297871837:ℚ)/5000000000),((14955508632498830776697252790141889196228967471972028940236307:ℚ)/395519173778300000000000000000000000000000000000000000000000000),((-649811241330393305929525639:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((866352229:ℚ)/1250000000),((7114639997:ℚ)/10000000000),((1170352229:ℚ)/2955000000),((27743919991:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((845570357:ℚ)/2000000000),((1343424675201093130519108812568769301159071842204981700632627:ℚ)/35770325345697070312500000000000000000000000000000000000000000),((-654142014631811218084272511:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((7050180693:ℚ)/10000000000),((904244003:ℚ)/1250000000),((9482180693:ℚ)/24020000000),((3512732009:ℚ)/7387500000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((765423631:ℚ)/2000000000),((135719392033660553630328961913274443967514732096572268902911:ℚ)/3634615830511120605468750000000000000000000000000000000000000),((-10288211645695292620088511:ℚ)/28880000000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/16),((3:ℚ)/8),((448095251:ℚ)/625000000),((294129857:ℚ)/400000000),((600095251:ℚ)/1525000000),((1138389571:ℚ)/2402000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3381849047:ℚ)/10000000000),((11977238222656280099447055068259047746467460565780998949:ℚ)/322298805966050000000000000000000000000000000000000000000),((-1060355011575216253635271:ℚ)/2957312000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((1822212181:ℚ)/2500000000),((759178557:ℚ)/1000000000),((2430212181:ℚ)/6290000000),((2917535671:ℚ)/6100000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((22970843:ℚ)/80000000),((5449009955612599242353196542659000014268008459607352739409:ℚ)/140317171595312500000000000000000000000000000000000000000000),((-6653007411252213196457471:ℚ)/18483200000000000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/16),((3:ℚ)/8),((3763722851:ℚ)/5000000000),((7830263401:ℚ)/10000000000),((553302539:ℚ)/1440000000),((29890790203:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1382884423:ℚ)/10000000000),((4860481615253451518628449085385583142631648007001300543797:ℚ)/125984458181250000000000000000000000000000000000000000000000),((-2783588453868607:ℚ)/7600000000000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/16),((3:ℚ)/8),((776597793:ℚ)/1000000000),((9736406271:ℚ)/10000000000),((1019797793:ℚ)/3200000000),((35609218813:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((722806043276468440806010524792857:ℚ)/12800000000000000000000000000000000),((-9425929:ℚ)/25600000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/16),((3:ℚ)/8),((9672462081:ℚ)/10000000000),((13543603233:ℚ)/10000000000),((12104462081:ℚ)/44160000000),((47030809699:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((78505660747657322873842963:ℚ)/975052800000000000000000000),((-9425929:ℚ)/25600000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source21 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC22
#check @N11Formalization.C450Source21GroupedC22.bound
#print axioms N11Formalization.C450Source21GroupedC22.valid0
#print axioms N11Formalization.C450Source21GroupedC22.valid1
#print axioms N11Formalization.C450Source21GroupedC22.valid2
#print axioms N11Formalization.C450Source21GroupedC22.valid3
#print axioms N11Formalization.C450Source21GroupedC22.valid4
#print axioms N11Formalization.C450Source21GroupedC22.valid5
#print axioms N11Formalization.C450Source21GroupedC22.valid6
#print axioms N11Formalization.C450Source21GroupedC22.valid7
#print axioms N11Formalization.C450Source21GroupedC22.valid8
#print axioms N11Formalization.C450Source21GroupedC22.valid9
#print axioms N11Formalization.C450Source21GroupedC22.valid10
#print axioms N11Formalization.C450Source21GroupedC22.bound
#print axioms N11Formalization.C450Source21GroupedC22.endpoint_checks
