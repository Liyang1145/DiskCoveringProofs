import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((1577565411:ℚ)/2500000000),((331100009:ℚ)/500000000),((-123100009:ℚ)/1240000000),((-412696233:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1182309797:ℚ)/2000000000),((572055858930685436989950868710593999877079707647022045133:ℚ)/3308060253906250000000000000000000000000000000000000000000),((-134100104276529436994387781:ℚ)/924160000000000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((818866103:ℚ)/1250000000),((3371159533:ℚ)/5000000000),((-1291159533:ℚ)/12875000000),((-296598309:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2658323453:ℚ)/5000000000),((61938818287847277096889324712463099920489493959505585777:ℚ)/362838827047729492187500000000000000000000000000000000000),((-36857049357604245640197549:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((3335587361:ℚ)/5000000000),((343129053:ℚ)/500000000),((-135129053:ℚ)/1311250000),((-455587361:ℚ)/17800000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4995751899:ℚ)/10000000000),((1578405671339103252621449134293161280691568466073770517571:ℚ)/9243906012500000000000000000000000000000000000000000000000),((-616512095297095194079097181:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((3395683211:ℚ)/5000000000),((6982789219:ℚ)/10000000000),((-2822789219:ℚ)/26700000000),((-1547049633:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((72733121:ℚ)/156250000),((45766165550700013765053048333947448393342748881205862297761:ℚ)/267910616641406250000000000000000000000000000000000000000000),((-1782292407171644516179821:ℚ)/10240000000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((431969177:ℚ)/625000000),((3521437003:ℚ)/5000000000),((-1326069:ℚ)/12500000),((-4233481:ℚ)/134375000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((67021247:ℚ)/156250000),((644109870032592210375768861467750067274367026539:ℚ)/3791189193725585937500000000000000000000000000000),((-10474995141584587441643469:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((6971558657:ℚ)/10000000000),((443934149:ℚ)/625000000),((-61311383:ℚ)/571093750),((-3634675971:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2047621349:ℚ)/5000000000),((16415082207418680172754026345864945087044828141754118903411:ℚ)/96579021552343750000000000000000000000000000000000000000000),((-2735728613183915543182120989:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((3515799329:ℚ)/5000000000),((7223055199:ℚ)/10000000000),((-3063055199:ℚ)/27650000000),((-635799329:ℚ)/18750000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((973016899:ℚ)/2500000000),((45670432413466329547491503635193089047904514994941286329:ℚ)/266987085342407226562500000000000000000000000000000000000),((-697488958651974340378430301:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((27936111:ℚ)/39062500),((7343118127:ℚ)/10000000000),((-3183118127:ℚ)/28125000000),((-16308333:ℚ)/446875000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((863014409:ℚ)/2500000000),((859435073748547402531304445234143254133495024908447:ℚ)/5019734001159667968750000000000000000000000000000000),((-44230701145966473744681:ℚ)/225625000000000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((7271646449:ℚ)/10000000000),((7583115361:ℚ)/10000000000),((-3423115361:ℚ)/28600000000),((-1511646449:ℚ)/39400000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((36877819:ℚ)/125000000),((215374831125128153363376426836697490368195913358792154023:ℚ)/1242373112500000000000000000000000000000000000000000000000),((-3007842581334498789631227261:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((1877881987:ℚ)/2500000000),((3911477361:ℚ)/5000000000),((-1831477361:ℚ)/14775000000),((-1313645961:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1527332027:ℚ)/10000000000),((18204950968657459352610827094844873141096415997830925881749:ℚ)/104801383593750000000000000000000000000000000000000000000000),((-201706448067886811523848709:ℚ)/924160000000000000000000000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((7751258993:ℚ)/10000000000),((129722131:ℚ)/156250000),((-64722131:ℚ)/476562500),((-1991258993:ℚ)/43200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1821958260573537426794390070286260408424118229198811297661:ℚ)/10245657600000000000000000000000000000000000000000000000000),((-229132887:ℚ)/1024000000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((329212943:ℚ)/400000000),((1276896839:ℚ)/1250000000),((-756896839:ℚ)/4050000000),((-296438829:ℚ)/6400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((26425166028176218487563803987537050061921328711014371591:ℚ)/132710400000000000000000000000000000000000000000000000000),((-229132887:ℚ)/1024000000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((10142684401:ℚ)/10000000000),((70151617:ℚ)/50000000),((-49351617:ℚ)/200000000),((-4382684401:ℚ)/73600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((434072621242827797951019523780526055867453693359076277657:ℚ)/1868851200000000000000000000000000000000000000000000000000),((-229132887:ℚ)/1024000000)⟩
theorem valid12 : Valid source28 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC13
#check @N11Formalization.C450Source28GroupedC13.bound
#print axioms N11Formalization.C450Source28GroupedC13.valid0
#print axioms N11Formalization.C450Source28GroupedC13.valid1
#print axioms N11Formalization.C450Source28GroupedC13.valid2
#print axioms N11Formalization.C450Source28GroupedC13.valid3
#print axioms N11Formalization.C450Source28GroupedC13.valid4
#print axioms N11Formalization.C450Source28GroupedC13.valid5
#print axioms N11Formalization.C450Source28GroupedC13.valid6
#print axioms N11Formalization.C450Source28GroupedC13.valid7
#print axioms N11Formalization.C450Source28GroupedC13.valid8
#print axioms N11Formalization.C450Source28GroupedC13.valid9
#print axioms N11Formalization.C450Source28GroupedC13.valid10
#print axioms N11Formalization.C450Source28GroupedC13.valid11
#print axioms N11Formalization.C450Source28GroupedC13.valid12
#print axioms N11Formalization.C450Source28GroupedC13.bound
#print axioms N11Formalization.C450Source28GroupedC13.endpoint_checks
