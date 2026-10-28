import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/16),((-1:ℚ)/8),((3120851641:ℚ)/5000000000),((1310397831:ℚ)/2000000000),((-603193493:ℚ)/19840000000),((1199148359:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((18973471:ℚ)/31250000),((577485478387388621250634812098349297:ℚ)/3813248000000000000000000000000000000),((-90388949093766325058491623:ℚ)/462080000000000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((6482694953:ℚ)/10000000000),((6672354739:ℚ)/10000000000),((-3377064217:ℚ)/103000000000),((2157305047:ℚ)/51500000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2745580637:ℚ)/5000000000),((498962913912184877931411527596528140976826824976328043:ℚ)/3334738159179687500000000000000000000000000000000000000),((-387682072449428705896835847:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((3301546963:ℚ)/5000000000),((849082713:ℚ)/1250000000),((-467248139:ℚ)/13112500000),((1018453037:ℚ)/26225000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((2589828889:ℚ)/5000000000),((16862794260902190243475906796934653382157286403214984393:ℚ)/112726625878906250000000000000000000000000000000000000000),((-100197629005899048066182127:ℚ)/462080000000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((6723433043:ℚ)/10000000000),((3456456601:ℚ)/5000000000),((-23026627:ℚ)/600000000),((1916566957:ℚ)/53400000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1212568137:ℚ)/2500000000),((427121747585697216458773407351845315908885649596210901411:ℚ)/2855124450000000000000000000000000000000000000000000000000),((-1146619389116021923153047:ℚ)/5120000000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((855464441:ℚ)/1250000000),((1758278041:ℚ)/2500000000),((-1114834123:ℚ)/27175000000),((224535559:ℚ)/6793750000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((562379913:ℚ)/1250000000),((54989113234746136172468924344438152383383188525214217:ℚ)/367459917926788330078125000000000000000000000000000000),((-6673431575959840963608423:ℚ)/28880000000000000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((6963944371:ℚ)/10000000000),((3576630657:ℚ)/5000000000),((-2409891971:ℚ)/55300000000),((1676055629:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4120332137:ℚ)/10000000000),((22608463732734832868877256222913907933542917971769725167:ℚ)/150993193750000000000000000000000000000000000000000000000),((-440300856540511226239190703:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((7084122357:ℚ)/10000000000),((909170399:ℚ)/1250000000),((-647511197:ℚ)/14062500000),((518625881:ℚ)/18750000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3705692011:ℚ)/10000000000),((6173657006278493488384517803530527882070836729786624381:ℚ)/41198730468750000000000000000000000000000000000000000000),((-453533563960947932883884767:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((90053151:ℚ)/125000000),((150268689:ℚ)/200000000),((-118006067:ℚ)/2288000000),((17946849:ℚ)/715000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3241308201:ℚ)/10000000000),((86458670607749400221688319547590189880976184193581:ℚ)/571134179687500000000000000000000000000000000000000),((-72937184829882284672983:ℚ)/288800000000000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((7444376253:ℚ)/10000000000),((1550668617:ℚ)/2000000000),((-1324005851:ℚ)/23640000000),((398541249:ℚ)/19700000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2027169271:ℚ)/10000000000),((21749144989000261563846098587789863450199944219919859663:ℚ)/143350743750000000000000000000000000000000000000000000000),((-493422835010969775728103247:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((1536866881:ℚ)/2000000000),((4116365387:ℚ)/5000000000),((-4029096161:ℚ)/61000000000),((191133119:ℚ)/12200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((439047900970535619810850263234390226527213038474675011:ℚ)/2837262500000000000000000000000000000000000000000000000),((-7074201:ℚ)/25600000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((510238261:ℚ)/625000000),((158532361:ℚ)/156250000),((-215597083:ℚ)/2025000000),((29761739:ℚ)/4050000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((13255650730033870880573205787473321255023348967767197:ℚ)/77847802734375000000000000000000000000000000000000000),((-7074201:ℚ)/25600000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((503831127:ℚ)/500000000),((218151007:ℚ)/156250000),((-394453021:ℚ)/2500000000),((-23943709:ℚ)/1840000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((5818563637659020792674599129447648336603367616411053:ℚ)/29200800000000000000000000000000000000000000000000000),((-7074201:ℚ)/25600000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC14
#check @N11Formalization.C450Source28GroupedC14.bound
#print axioms N11Formalization.C450Source28GroupedC14.valid0
#print axioms N11Formalization.C450Source28GroupedC14.valid1
#print axioms N11Formalization.C450Source28GroupedC14.valid2
#print axioms N11Formalization.C450Source28GroupedC14.valid3
#print axioms N11Formalization.C450Source28GroupedC14.valid4
#print axioms N11Formalization.C450Source28GroupedC14.valid5
#print axioms N11Formalization.C450Source28GroupedC14.valid6
#print axioms N11Formalization.C450Source28GroupedC14.valid7
#print axioms N11Formalization.C450Source28GroupedC14.valid8
#print axioms N11Formalization.C450Source28GroupedC14.valid9
#print axioms N11Formalization.C450Source28GroupedC14.valid10
#print axioms N11Formalization.C450Source28GroupedC14.valid11
#print axioms N11Formalization.C450Source28GroupedC14.bound
#print axioms N11Formalization.C450Source28GroupedC14.endpoint_checks
