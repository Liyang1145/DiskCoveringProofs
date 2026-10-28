import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC17
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨(0:ℚ),((1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),(0:ℚ),((1:ℚ)/16),((6127008997:ℚ)/10000000000),((6647979019:ℚ)/10000000000),((8:ℚ)/89),((16887979019:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6331200889:ℚ)/10000000000),((54281023470657053565949325097164346324319:ℚ)/966551597056000000000000000000000000000000),((-1985617841171230763053042901:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),(0:ℚ),((1:ℚ)/16),((6604367913:ℚ)/10000000000),((6886410987:ℚ)/10000000000),((48:ℚ)/553),((17126410987:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((323516943:ℚ)/625000000),((188360093260833507833026981549424119979722219627129981358324063:ℚ)/3492491011720200000000000000000000000000000000000000000000000000),((-6419801793697836145840263487:ℚ)/44359680000000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),(0:ℚ),((1:ℚ)/16),((273716999:ℚ)/400000000),((7005603229:ℚ)/10000000000),((32:ℚ)/375),((17245603229:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((900286129:ℚ)/2000000000),((288441701133195717438527868993300487989227902053488647541:ℚ)/5435754975000000000000000000000000000000000000000000000000),((-2217034156057227694180238181:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),(0:ℚ),((1:ℚ)/16),((1740544139:ℚ)/2500000000),((7124780701:ℚ)/10000000000),((12:ℚ)/143),((17364780701:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((257883537:ℚ)/625000000),((436598382479263173173670051078893565651272434303920583507393:ℚ)/8271551513671875000000000000000000000000000000000000000000000),((-2255213178653099098136157541:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((3540705687:ℚ)/5000000000),((7243944133:ℚ)/10000000000),((96:ℚ)/1163),((17483944133:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((743105881:ℚ)/2000000000),((249313912189322516254258722777179702609110692853163000180482537:ℚ)/4746230085339600000000000000000000000000000000000000000000000000),((-2293374798959655656027148149:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),(0:ℚ),((1:ℚ)/16),((3600315129:ℚ)/5000000000),((3681547103:ℚ)/5000000000),((16:ℚ)/197),((8801547103:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3256238237:ℚ)/10000000000),((935382123413881331804423985404096708502785136634898785460243:ℚ)/17885162672848535156250000000000000000000000000000000000000000),((-30677885359789418218255151:ℚ)/194560000000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((365991699:ℚ)/500000000),((7482231559:ℚ)/10000000000),((96:ℚ)/1201),((17722231559:ℚ)/118200000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((272369951:ℚ)/1000000000),((1163297952195780348037807398049510430269933456504464003524370331:ℚ)/22331079662660325000000000000000000000000000000000000000000000000),((-6564118824306178486717861:ℚ)/40960000000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),(0:ℚ),((1:ℚ)/16),((7439023267:ℚ)/10000000000),((7601356789:ℚ)/10000000000),((24:ℚ)/305),((17841356789:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2061860707:ℚ)/10000000000),((1045641713304875564296392933234516108321386438159177194551547:ℚ)/20143675372878125000000000000000000000000000000000000000000000),((-31681139330420201:ℚ)/194560000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(0:ℚ),((1:ℚ)/16),((7558198797:ℚ)/10000000000),((8077747213:ℚ)/10000000000),((2:ℚ)/27),((18317747213:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((65581579:ℚ)/625000000),((54030446692331398089386392800931486572130909037174293028219:ℚ)/1034182181250000000000000000000000000000000000000000000000000),((-32192545722282791:ℚ)/194560000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(0:ℚ),((1:ℚ)/16),((502173471:ℚ)/625000000),((9981983773:ℚ)/10000000000),((3:ℚ)/50),((20221983773:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((67935416424970647036577708902739266671263113386103153937:ℚ)/1275458400000000000000000000000000000000000000000000000000),((-170378543:ℚ)/1024000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(0:ℚ),((1:ℚ)/16),((9939579147:ℚ)/10000000000),((6893475177:ℚ)/5000000000),((1:ℚ)/23),((12013475177:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2026441061204373844153637581620934045597:ℚ)/33856000000000000000000000000000000000000),((-170378543:ℚ)/1024000000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC17
#check @N11Formalization.C450Source17GroupedC17.bound
#print axioms N11Formalization.C450Source17GroupedC17.valid0
#print axioms N11Formalization.C450Source17GroupedC17.valid1
#print axioms N11Formalization.C450Source17GroupedC17.valid2
#print axioms N11Formalization.C450Source17GroupedC17.valid3
#print axioms N11Formalization.C450Source17GroupedC17.valid4
#print axioms N11Formalization.C450Source17GroupedC17.valid5
#print axioms N11Formalization.C450Source17GroupedC17.valid6
#print axioms N11Formalization.C450Source17GroupedC17.valid7
#print axioms N11Formalization.C450Source17GroupedC17.valid8
#print axioms N11Formalization.C450Source17GroupedC17.valid9
#print axioms N11Formalization.C450Source17GroupedC17.valid10
#print axioms N11Formalization.C450Source17GroupedC17.bound
#print axioms N11Formalization.C450Source17GroupedC17.endpoint_checks
