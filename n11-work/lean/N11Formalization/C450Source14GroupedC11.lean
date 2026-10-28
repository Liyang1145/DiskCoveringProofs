import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((6333211137:ℚ)/10000000000),((6614426087:ℚ)/10000000000),((-16003278261:ℚ)/49600000000),((-4669211137:ℚ)/20600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5857146301:ℚ)/10000000000),((243204838537555204167675010284363199148667915311098711051:ℚ)/5081180550000000000000000000000000000000000000000000000000),((230139801317798251795718747:ℚ)/2957312000000000000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((3285666061:ℚ)/5000000000),((6852570881:ℚ)/10000000000),((-16717712643:ℚ)/51500000000),((-817888687:ℚ)/3560000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5263451281:ℚ)/10000000000),((345500059015338294548033675741306115162426347457293551:ℚ)/7261180700000000000000000000000000000000000000000000000),((55673581071253400250159123:ℚ)/739328000000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((1361881751:ℚ)/2000000000),((3485813153:ℚ)/5000000000),((-2845813153:ℚ)/8900000000),((-1029081751:ℚ)/4348000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1150437257:ℚ)/2500000000),((2127789677749273247872772337880062626890718105291262321:ℚ)/45723411906800000000000000000000000000000000000000000000),((8609849566454805580202763:ℚ)/118292480000000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((69284319:ℚ)/100000000),((1406230007:ℚ)/2000000000),((-3450690021:ℚ)/10870000000),((-52644319:ℚ)/219300000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4235496689:ℚ)/10000000000),((274949474621002438469675377088528516068997450346949:ℚ)/5970960668207812500000000000000000000000000000000000),((21152117354775843343643:ℚ)/295731200000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((6987939911:ℚ)/10000000000),((7090671199:ℚ)/10000000000),((-5810671199:ℚ)/18275000000),((-5323939911:ℚ)/22120000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4040767641:ℚ)/10000000000),((35548803855890676901887452908110111903900434138312646651:ℚ)/772632172418750000000000000000000000000000000000000000000),((209658377846079667397727723:ℚ)/2957312000000000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((704744563:ℚ)/1000000000),((893773733:ℚ)/1250000000),((-314474457:ℚ)/987500000),((-538344563:ℚ)/2231000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((959185879:ℚ)/2500000000),((15754147782759708280801613422038581751647255301592763:ℚ)/342677694878515625000000000000000000000000000000000000),((2077954043431613117635347:ℚ)/29573120000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((3553474557:ℚ)/5000000000),((1441941219:ℚ)/2000000000),((-3557823657:ℚ)/11155000000),((-2721474557:ℚ)/11250000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((905462413:ℚ)/2500000000),((10688022465011124819610740334020496278156041741033278591:ℚ)/232658243179321289062500000000000000000000000000000000000),((51483062820738569137223987:ℚ)/739328000000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((3583225211:ℚ)/5000000000),((454326247:ℚ)/625000000),((-374326247:ℚ)/1171875000),((-2751225211:ℚ)/11345000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((169700879:ℚ)/500000000),((1047357283470388813482366906788139367943032855166581:ℚ)/22815685759765625000000000000000000000000000000000000),((51017229211454096111063523:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((903243701:ℚ)/1250000000),((1465746299:ℚ)/2000000000),((-3629238897:ℚ)/11345000000),((-695243701:ℚ)/2860000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3150436869:ℚ)/10000000000),((15218385306985637260664266374183097073567844108454368991:ℚ)/331751284150000000000000000000000000000000000000000000000),((3159459365120711776920963:ℚ)/46208000000000000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((291417869:ℚ)/400000000),((7388240781:ℚ)/10000000000),((-18324722343:ℚ)/57200000000),((-74952623:ℚ)/307600000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((577423831:ℚ)/2000000000),((139739374506874187896848594739651849015918352653:ℚ)/3048290394703125000000000000000000000000000000000),((320546715544126966989843:ℚ)/4731699200000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((28691179:ℚ)/39062500),((1489549573:ℚ)/2000000000),((-1233549573:ℚ)/3845000000),((-22191179:ℚ)/90859375),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2598064669:ℚ)/10000000000),((660626598822663456748689077202782763096894946247709:ℚ)/14420342772519588470458984375000000000000000000000000),((3028531018311257697783:ℚ)/45125000000000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((1851108739:ℚ)/2500000000),((1513351129:ℚ)/2000000000),((-3772053387:ℚ)/11630000000),((-1435108739:ℚ)/5910000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((454694309:ℚ)/2000000000),((641075892378235605784040058468312114751418802925981349:ℚ)/13893076248437500000000000000000000000000000000000000000),((12288358287371238971446323:ℚ)/184832000000000000000000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((1504683101:ℚ)/2000000000),((3902373521:ℚ)/5000000000),((-3262373521:ℚ)/9850000000),((-1171883101:ℚ)/4880000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((355209039:ℚ)/2500000000),((20077713053344912648076785901944105072120902059487067109:ℚ)/429266467200000000000000000000000000000000000000000000000),((7715400438945998551605363:ℚ)/118292480000000000000000000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((3880677501:ℚ)/5000000000),((8280643143:ℚ)/10000000000),((-21001929429:ℚ)/61000000000),((-3048677501:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((13253347904228147449209214154482094939304616664141923733:ℚ)/276632755200000000000000000000000000000000000000000000000),((13191441:ℚ)/204800000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((4118578241:ℚ)/5000000000),((2036674899:ℚ)/2000000000),((-1780674899:ℚ)/4320000000),((-3286578241:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((12424901669632713891206879903579869977017052025770349231:ℚ)/230400000000000000000000000000000000000000000000000000000),((13191441:ℚ)/204800000)⟩
theorem valid14 : Valid source14 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((10139599589:ℚ)/10000000000),((13986578049:ℚ)/10000000000),((-38119734147:ℚ)/80000000000),((-2825199863:ℚ)/14720000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((915402373104566914526255284023523588415593993203195659:ℚ)/14950809600000000000000000000000000000000000000000000000),((13191441:ℚ)/204800000)⟩
theorem valid15 : Valid source14 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source14 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source14 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source14 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source14 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source14 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source14 nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC11
#check @N11Formalization.C450Source14GroupedC11.bound
#print axioms N11Formalization.C450Source14GroupedC11.valid0
#print axioms N11Formalization.C450Source14GroupedC11.valid1
#print axioms N11Formalization.C450Source14GroupedC11.valid2
#print axioms N11Formalization.C450Source14GroupedC11.valid3
#print axioms N11Formalization.C450Source14GroupedC11.valid4
#print axioms N11Formalization.C450Source14GroupedC11.valid5
#print axioms N11Formalization.C450Source14GroupedC11.valid6
#print axioms N11Formalization.C450Source14GroupedC11.valid7
#print axioms N11Formalization.C450Source14GroupedC11.valid8
#print axioms N11Formalization.C450Source14GroupedC11.valid9
#print axioms N11Formalization.C450Source14GroupedC11.valid10
#print axioms N11Formalization.C450Source14GroupedC11.valid11
#print axioms N11Formalization.C450Source14GroupedC11.valid12
#print axioms N11Formalization.C450Source14GroupedC11.valid13
#print axioms N11Formalization.C450Source14GroupedC11.valid14
#print axioms N11Formalization.C450Source14GroupedC11.valid15
#print axioms N11Formalization.C450Source14GroupedC11.bound
#print axioms N11Formalization.C450Source14GroupedC11.endpoint_checks
