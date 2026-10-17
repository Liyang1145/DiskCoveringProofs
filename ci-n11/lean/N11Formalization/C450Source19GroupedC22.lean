import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC22
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((5:ℚ)/16),((3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/16),((3:ℚ)/8),((47151743:ℚ)/80000000),((3215586137:ℚ)/5000000000),((64559743:ℚ)/170880000),((404088981:ℚ)/800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((273301869:ℚ)/400000000),((35756901424507511099:ℚ)/973332480000000000000),((-65920091085336292604050599:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((50972363:ℚ)/80000000),((6669753449:ℚ)/10000000000),((68380363:ℚ)/176960000),((8589753449:ℚ)/17800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((230610547:ℚ)/400000000),((1027410576791766588513695307279971807380703212057367473262839:ℚ)/32337879738150000000000000000000000000000000000000000000000000),((-271953747812532513282433671:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((5:ℚ)/16),((3:ℚ)/8),((6610200303:ℚ)/10000000000),((6908262339:ℚ)/10000000000),((8786200303:ℚ)/22880000000),((26484787017:ℚ)/55300000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5160740819:ℚ)/10000000000),((7368623286288564023945869251296619445108122456143216767119:ℚ)/237512293768750000000000000000000000000000000000000000000000),((-275662400107099812114381391:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((6848777983:ℚ)/10000000000),((7027491909:ℚ)/10000000000),((9024777983:ℚ)/23260000000),((26842475727:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4483697739:ℚ)/10000000000),((11501700898401595068737447676065544378071530268346920016547251:ℚ)/395519173778300000000000000000000000000000000000000000000000000),((-279770012409943156565589951:ℚ)/924160000000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((6968040241:ℚ)/10000000000),((1786676493:ℚ)/2500000000),((9144040241:ℚ)/23640000000),((6800029479:ℚ)/14537500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2053427007:ℚ)/5000000000),((5375945472682681924561915110485328624609307438812123750947:ℚ)/186303777842172241210937500000000000000000000000000000000000),((-17600324515443868499866479:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((7087285927:ℚ)/10000000000),((1816476317:ℚ)/2500000000),((9263285927:ℚ)/24020000000),((2296476317:ℚ)/4925000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((46177259:ℚ)/125000000),((92597913186371991688343685249110831836260961818076105858387:ℚ)/3230769627120996093750000000000000000000000000000000000000000),((-17714555892027134268592719:ℚ)/57760000000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/16),((3:ℚ)/8),((1441303167:ℚ)/2000000000),((1846272623:ℚ)/2500000000),((30762347:ℚ)/80000000),((6978817869:ℚ)/15012500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((646388533:ℚ)/2000000000),((602567864131963895548326232334416268519653324059309357:ℚ)/21146528332519531250000000000000000000000000000000000000),((-17828320852227297832543159:ℚ)/57760000000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((3662865353:ℚ)/5000000000),((1524684259:ℚ)/2000000000),((4750865353:ℚ)/12580000000),((5726052777:ℚ)/12200000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((2694707277:ℚ)/10000000000),((33221385528800055880285002681732798671424423590930007386949:ℚ)/1122537372762500000000000000000000000000000000000000000000000),((-992724138182313:ℚ)/3200000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/16),((3:ℚ)/8),((945514761:ℚ)/1250000000),((7861703137:ℚ)/10000000000),((1217514761:ℚ)/3240000000),((29345109411:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((486056789:ℚ)/5000000000),((99822863158877786173384068145051967662409377084049976609509:ℚ)/3401580370893750000000000000000000000000000000000000000000000),((-4789879066439339:ℚ)/15200000000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/16),((3:ℚ)/8),((1950613289:ℚ)/2500000000),((1220827001:ℚ)/1250000000),((2494613289:ℚ)/8000000000),((1460827001:ℚ)/2700000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1988959946114907812769361095336169:ℚ)/48000000000000000000000000000000000),((-20215089:ℚ)/64000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/16),((3:ℚ)/8),((9707700133:ℚ)/10000000000),((6786187093:ℚ)/5000000000),((11883700133:ℚ)/44160000000),((23238561279:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((3765689347639763209732739:ℚ)/65003520000000000000000000),((-20215089:ℚ)/64000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source19 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC22
#check @N11Formalization.C450Source19GroupedC22.bound
#print axioms N11Formalization.C450Source19GroupedC22.valid0
#print axioms N11Formalization.C450Source19GroupedC22.valid1
#print axioms N11Formalization.C450Source19GroupedC22.valid2
#print axioms N11Formalization.C450Source19GroupedC22.valid3
#print axioms N11Formalization.C450Source19GroupedC22.valid4
#print axioms N11Formalization.C450Source19GroupedC22.valid5
#print axioms N11Formalization.C450Source19GroupedC22.valid6
#print axioms N11Formalization.C450Source19GroupedC22.valid7
#print axioms N11Formalization.C450Source19GroupedC22.valid8
#print axioms N11Formalization.C450Source19GroupedC22.valid9
#print axioms N11Formalization.C450Source19GroupedC22.valid10
#print axioms N11Formalization.C450Source19GroupedC22.bound
#print axioms N11Formalization.C450Source19GroupedC22.endpoint_checks
