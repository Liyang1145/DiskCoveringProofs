import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC23
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((3:ℚ)/8),((7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/8),((7:ℚ)/16),((751819717:ℚ)/1250000000),((3265826043:ℚ)/5000000000),((871819717:ℚ)/2225000000),((26060782301:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1644295533:ℚ)/2500000000),((4827475814972217443611:ℚ)/618828125000000000000000),((-2055104927145308241500411:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((6490301941:ℚ)/10000000000),((1353887849:ℚ)/2000000000),((22350905823:ℚ)/55300000000),((10757214943:ℚ)/21360000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5471953971:ℚ)/10000000000),((65126650106033474322368550613485671:ℚ)/11467837500000000000000000000000000000),((-371740026112019167048579:ℚ)/2560000000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/8),((7:ℚ)/16),((6728135607:ℚ)/10000000000),((6888325537:ℚ)/10000000000),((2562711869:ℚ)/6250000000),((54618278759:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2418492167:ℚ)/5000000000),((5740275144455186762368772779516930411295709737217548543:ℚ)/1207945550000000000000000000000000000000000000000000000000),((-135541202691240741919722051:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/8),((7:ℚ)/16),((6847043971:ℚ)/10000000000),((3503603647:ℚ)/5000000000),((23421131913:ℚ)/57200000000),((9241741843:ℚ)/18750000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2244479047:ℚ)/5000000000),((3899808047707358939248820632369197413672316817393860883957:ℚ)/842472839355468750000000000000000000000000000000000000000000),((-136214569129242201965975659:ℚ)/924160000000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/8),((7:ℚ)/16),((870743383:ℚ)/1250000000),((7066646543:ℚ)/10000000000),((990743383:ℚ)/2403125000),((55866525801:ℚ)/114400000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2056873577:ℚ)/5000000000),((5824985979951690939806282218602433389591204261524956543276751:ℚ)/1383409580581600000000000000000000000000000000000000000000000000),((-2138893187419548992875811:ℚ)/14440000000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((1405079343:ℚ)/2000000000),((356304237:ℚ)/500000000),((4791238029:ℚ)/11630000000),((2814129659:ℚ)/5767500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3913517259:ℚ)/10000000000),((90004649344314936339964790512042483829996421783326261407:ℚ)/21624246980104253906250000000000000000000000000000000000000),((-5489076899873428823068851:ℚ)/36966400000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/8),((7:ℚ)/16),((1416969029:ℚ)/2000000000),((7185521911:ℚ)/10000000000),((4826907087:ℚ)/11725000000),((56698653377:ℚ)/116300000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3703065009:ℚ)/10000000000),((6676563705943990626684154796877624321172293110808344027185981:ℚ)/1621907605630626562500000000000000000000000000000000000000000000),((-5502599543771030121221659:ℚ)/36966400000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((3572146191:ℚ)/5000000000),((3622479041:ℚ)/5000000000),((4052146191:ℚ)/9850000000),((28557353287:ℚ)/58625000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1740266213:ℚ)/5000000000),((49768515076663540407175034906424028101012473416764178818833:ℚ)/12218026014956665039062500000000000000000000000000000000000000),((-34475840606810302251596019:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/8),((7:ℚ)/16),((7203738457:ℚ)/10000000000),((292175731:ℚ)/400000000),((24491215371:ℚ)/59575000000),((2301230117:ℚ)/4728000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((648685903:ℚ)/2000000000),((45382296431707431287925397477100720638291507334750055303001:ℚ)/11253348288114422400000000000000000000000000000000000000000000),((-138242044153494823207039651:ℚ)/924160000000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((1815795849:ℚ)/2500000000),((1472765503:ℚ)/2000000000),((6167387547:ℚ)/15012500000),((11589358521:ℚ)/23830000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2988285329:ℚ)/10000000000),((30457801782132929845109350650622598435325972821864373260311:ℚ)/7624619518642455859375000000000000000000000000000000000000000),((-8661314618933099000013699:ℚ)/57760000000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/8),((7:ℚ)/16),((3661313613:ℚ)/5000000000),((7482693223:ℚ)/10000000000),((12423940839:ℚ)/30500000000),((58778852561:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((542000753:ℚ)/2000000000),((171186284802171844052840008743132367372386198481168688289511:ℚ)/40287350745756250000000000000000000000000000000000000000000000),((-34730082952924889773606731:ℚ)/231040000000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((3720755833:ℚ)/5000000000),((7720414139:ℚ)/10000000000),((12602267499:ℚ)/31450000000),((60442898973:ℚ)/122000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((511451533:ℚ)/2500000000),((5310681973305354821593321217581653688753996203695136399884507:ℚ)/1122537372762500000000000000000000000000000000000000000000000000),((-34899963162249692959536611:ℚ)/231040000000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/8),((7:ℚ)/16),((7679268343:ℚ)/10000000000),((3979061041:ℚ)/5000000000),((8639268343:ℚ)/21600000000),((31053427287:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((5216066991067436990657705994025410809532796865207265239873:ℚ)/1133860123631250000000000000000000000000000000000000000000000),((-194609:ℚ)/1280000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/8),((7:ℚ)/16),((3958504973:ℚ)/5000000000),((9859429701:ℚ)/10000000000),((13315514919:ℚ)/40000000000),((75416007907:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((15208234304003660815954521255044507:ℚ)/1500000000000000000000000000000000000),((-194609:ℚ)/1280000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/8),((7:ℚ)/16),((4909264577:ℚ)/5000000000),((6830482043:ℚ)/5000000000),((5389264577:ℚ)/18400000000),((51013374301:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((685734280454371867186771:ℚ)/42320000000000000000000000),((-194609:ℚ)/1280000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source11 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC23
#check @N11Formalization.C450Source11GroupedC23.bound
#print axioms N11Formalization.C450Source11GroupedC23.valid0
#print axioms N11Formalization.C450Source11GroupedC23.valid1
#print axioms N11Formalization.C450Source11GroupedC23.valid2
#print axioms N11Formalization.C450Source11GroupedC23.valid3
#print axioms N11Formalization.C450Source11GroupedC23.valid4
#print axioms N11Formalization.C450Source11GroupedC23.valid5
#print axioms N11Formalization.C450Source11GroupedC23.valid6
#print axioms N11Formalization.C450Source11GroupedC23.valid7
#print axioms N11Formalization.C450Source11GroupedC23.valid8
#print axioms N11Formalization.C450Source11GroupedC23.valid9
#print axioms N11Formalization.C450Source11GroupedC23.valid10
#print axioms N11Formalization.C450Source11GroupedC23.valid11
#print axioms N11Formalization.C450Source11GroupedC23.valid12
#print axioms N11Formalization.C450Source11GroupedC23.valid13
#print axioms N11Formalization.C450Source11GroupedC23.valid14
#print axioms N11Formalization.C450Source11GroupedC23.bound
#print axioms N11Formalization.C450Source11GroupedC23.endpoint_checks
