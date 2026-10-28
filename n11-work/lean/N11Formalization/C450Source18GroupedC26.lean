import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((5752234411:ℚ)/10000000000),((1258798633:ℚ)/2000000000),((62010109699:ℚ)/106800000000),((1476398633:ℚ)/1984000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7122811881:ℚ)/10000000000),((-2037808599650617442234077932733991971:ℚ)/152273304000000000000000000000000000000),((-9357397046407641883733039:ℚ)/29573120000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((311442989:ℚ)/500000000),((163305427:ℚ)/250000000),((3314986901:ℚ)/5530000000),((63501809:ℚ)/89000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6101068313:ℚ)/10000000000),((-408069820186642664747184490797768914719360617580939:ℚ)/20068715625000000000000000000000000000000000000000000),((-147128563722583729822679:ℚ)/462080000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((3233544153:ℚ)/5000000000),((6770392699:ℚ)/10000000000),((34221897377:ℚ)/57200000000),((7858392699:ℚ)/11060000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((2765189951:ℚ)/5000000000),((-12154847104107137155635696111045661322616244027953892779:ℚ)/584841400000000000000000000000000000000000000000000000000),((-235893265553706614073443751:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((268210729:ℚ)/400000000),((1722365971:ℚ)/2500000000),((2823496561:ℚ)/4652000000),((153412767:ℚ)/220000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4901290123:ℚ)/10000000000),((-5596042884586564864594140841862840358860797484078201:ℚ)/235955662050000000000000000000000000000000000000000000),((-14788326280995491675707991:ℚ)/46208000000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((1364868291:ℚ)/2000000000),((3504262351:ℚ)/5000000000),((14331814619:ℚ)/23640000000),((4048262351:ℚ)/5815000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1139326797:ℚ)/2500000000),((-737253724148633723593386078203662468160495286977756491:ℚ)/30963760650000000000000000000000000000000000000000000000),((-59211549257871709315776351:ℚ)/184832000000000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((6943404251:ℚ)/10000000000),((7127575649:ℚ)/10000000000),((72730638259:ℚ)/120100000000),((8215575649:ℚ)/11820000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((4187305833:ℚ)/10000000000),((-387944612470036184432095764398122430723987869748650010219:ℚ)/16240533759375000000000000000000000000000000000000000000000),((-237074875792385202552100351:ℚ)/739328000000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((7062457113:ℚ)/10000000000),((1811654297:ℚ)/2500000000),((73802114017:ℚ)/122000000000),((2083654297:ℚ)/3002500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3783627703:ℚ)/10000000000),((-135898907830638483503603149446009605612080650353629631611:ℚ)/5674525000000000000000000000000000000000000000000000000000),((-14831203678526516087636559:ℚ)/46208000000000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((7181500507:ℚ)/10000000000),((7365649753:ℚ)/10000000000),((74873504563:ℚ)/123900000000),((8453649753:ℚ)/12200000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1667013049:ℚ)/5000000000),((-11885368304466392651960726790609320252290027850954231963:ℚ)/495316385156250000000000000000000000000000000000000000000),((-237519348161455238940753359:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((730053487:ℚ)/1000000000),((7484673753:ℚ)/10000000000),((446734199:ℚ)/740000000),((1224667679:ℚ)/1770000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2816552173:ℚ)/10000000000),((-29713866810840170735352333002944854200680587477:ℚ)/1236645507812500000000000000000000000000000000000),((-237735145521830857456497359:ℚ)/739328000000000000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((7419560613:ℚ)/10000000000),((1930674393:ℚ)/2500000000),((77016045517:ℚ)/129600000000),((2202674393:ℚ)/3145000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2183418023:ℚ)/10000000000),((-5483855869931092143803024658658778324322187430780408677:ℚ)/251942400000000000000000000000000000000000000000000000000),((-39137354364459057:ℚ)/121600000000000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((1914396941:ℚ)/2500000000),((9625990189:ℚ)/10000000000),((19789572469:ℚ)/40000000000),((3571330063:ℚ)/4320000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((5120527581907388704194763820934137:ℚ)/6000000000000000000000000000000000000),((-82647649:ℚ)/256000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((9560901309:ℚ)/10000000000),((13429851343:ℚ)/10000000000),((96288111781:ℚ)/220800000000),((14517851343:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((469721024656753671644483249:ℚ)/24376320000000000000000000000),((-82647649:ℚ)/256000000)⟩
theorem valid11 : Valid source18 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source18 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC26
#check @N11Formalization.C450Source18GroupedC26.bound
#print axioms N11Formalization.C450Source18GroupedC26.valid0
#print axioms N11Formalization.C450Source18GroupedC26.valid1
#print axioms N11Formalization.C450Source18GroupedC26.valid2
#print axioms N11Formalization.C450Source18GroupedC26.valid3
#print axioms N11Formalization.C450Source18GroupedC26.valid4
#print axioms N11Formalization.C450Source18GroupedC26.valid5
#print axioms N11Formalization.C450Source18GroupedC26.valid6
#print axioms N11Formalization.C450Source18GroupedC26.valid7
#print axioms N11Formalization.C450Source18GroupedC26.valid8
#print axioms N11Formalization.C450Source18GroupedC26.valid9
#print axioms N11Formalization.C450Source18GroupedC26.valid10
#print axioms N11Formalization.C450Source18GroupedC26.valid11
#print axioms N11Formalization.C450Source18GroupedC26.bound
#print axioms N11Formalization.C450Source18GroupedC26.endpoint_checks
