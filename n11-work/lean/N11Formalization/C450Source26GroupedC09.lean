import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((3279804553:ℚ)/5000000000),((6759121471:ℚ)/10000000000),((-4839121471:ℚ)/12400000000),((-14958631871:ℚ)/50550000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((529407473:ℚ)/1000000000),((16484304905405972263292273656023124619361031668828922568443:ℚ)/75080377174218750000000000000000000000000000000000000000000),((9035836398870744075644093:ℚ)/73932800000000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((1335900979:ℚ)/2000000000),((3439490801:ℚ)/5000000000),((-2479490801:ℚ)/6318750000),((-6151306853:ℚ)/20600000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((621602957:ℚ)/1250000000),((4042822213305665598594998425102005419992210709207454162221:ℚ)/18412449950000000000000000000000000000000000000000000000000),((1383353202363792372351157:ℚ)/11829248000000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((3399678911:ℚ)/5000000000),((3499400487:ℚ)/5000000000),((-2539400487:ℚ)/6437500000),((-15797752377:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4631438959:ℚ)/10000000000),((5099296902896324608515433474174640515233479358920950755719:ℚ)/23221684931054687500000000000000000000000000000000000000000),((22862648152923738332197:ℚ)/204800000000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((6919170257:ℚ)/10000000000),((7058696073:ℚ)/10000000000),((-5138696073:ℚ)/13112500000),((-32434191799:ℚ)/105850000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1066262619:ℚ)/2500000000),((1684800553791594468917055706498356127503533600005850872971679:ℚ)/7775495826591406250000000000000000000000000000000000000000000),((31432827858153307220762573:ℚ)/295731200000000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((218095687:ℚ)/312500000),((7118581799:ℚ)/10000000000),((-5198581799:ℚ)/13231250000),((-1026669809:ℚ)/3337500000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((1017594049:ℚ)/2500000000),((26652161044961877919558542787483283427250178558160579557:ℚ)/122971566989135742187500000000000000000000000000000000000),((29920315348417553312413:ℚ)/288800000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/2),((-7:ℚ)/16),((17597361:ℚ)/25000000),((3589229203:ℚ)/5000000000),((-2629229203:ℚ)/6675000000),((-83181527:ℚ)/269375000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3866516021:ℚ)/10000000000),((9207404184112108479623861878044960976913628763563:ℚ)/42471922630071640014648437500000000000000000000000),((559524447250699299751:ℚ)/5544960000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((1419763551:ℚ)/2000000000),((1447665227:ℚ)/2000000000),((-1063665227:ℚ)/2693750000),((-6738344857:ℚ)/21740000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3651926777:ℚ)/10000000000),((6001762269926737546280094998921132651069317419421707410367:ℚ)/27678076589650000000000000000000000000000000000000000000000),((3484983435304015072127431:ℚ)/35487744000000000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((1789670573:ℚ)/2500000000),((7298185221:ℚ)/10000000000),((-5378185221:ℚ)/13587500000),((-8527694011:ℚ)/27412500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((3424586751:ℚ)/10000000000),((2529441010092812924811591271881238897926608732619909598631:ℚ)/11662032555093383789062500000000000000000000000000000000000),((1764942202872888701334133:ℚ)/18483200000000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((3609269121:ℚ)/5000000000),((7358035891:ℚ)/10000000000),((-5438035891:ℚ)/13706250000),((-17264883847:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((636351647:ℚ)/2000000000),((2619088572884089425104719406092452064674717343582123035053:ℚ)/12072377694042968750000000000000000000000000000000000000000),((20575456373611967522993671:ℚ)/221798400000000000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/2),((-7:ℚ)/16),((909798229:ℚ)/1250000000),((7477712849:ℚ)/10000000000),((-5557712849:ℚ)/13825000000),((-4368587603:ℚ)/14062500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2919572993:ℚ)/10000000000),((24748995090065705057410773170941107713782499273035369417:ℚ)/112635176628828048706054687500000000000000000000000000000),((416033226838436647457157:ℚ)/4620800000000000000000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((7398056787:ℚ)/10000000000),((3798679333:ℚ)/5000000000),((-2838679333:ℚ)/7031250000),((-35786397509:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5776027:ℚ)/25000000),((1682561123439875913467799386045745752446115918594023807199:ℚ)/7656105600000000000000000000000000000000000000000000000000),((75007329705293554637260639:ℚ)/887193600000000000000000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-1:ℚ)/2),((-7:ℚ)/16),((7517696807:ℚ)/10000000000),((201891501:ℚ)/250000000),((-153891501:ℚ)/357500000),((-36623877649:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((1473022067:ℚ)/10000000000),((1143331334511694150897132096823346873634851082333099487025589:ℚ)/4868742450000000000000000000000000000000000000000000000000000),((64731334920576360433493:ℚ)/819200000000000000000000)⟩
theorem valid11 : Valid source26 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source26 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((62468569:ℚ)/78125000),((8553570639:ℚ)/10000000000),((-6633570639:ℚ)/15250000000),((-312279983:ℚ)/1012500000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((30831909640823804640654344686912418184173829952411561:ℚ)/131908776855468750000000000000000000000000000000000000),((38499247:ℚ)/512000000)⟩
theorem valid12 : Valid source26 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((8473868633:ℚ)/10000000000),((418497177:ℚ)/400000000),((-12655451:ℚ)/24000000),((-43317080431:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((21402684265094474200047448098277831478518604843698628252797:ℚ)/76800000000000000000000000000000000000000000000000000000000),((38499247:ℚ)/512000000)⟩
theorem valid13 : Valid source26 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((5191335161:ℚ)/5000000000),((7136399641:ℚ)/5000000000),((-6176399641:ℚ)/10000000000),((-9446448709:ℚ)/36800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((75885792121768047762891974588991107689596675134399185583:ℚ)/233606400000000000000000000000000000000000000000000000000),((38499247:ℚ)/512000000)⟩
theorem valid14 : Valid source26 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source26 nn0 nn1 Qcell ((1011:ℚ)/1600) ((1049:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source26 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source26 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC09
#check @N11Formalization.C450Source26GroupedC09.bound
#print axioms N11Formalization.C450Source26GroupedC09.valid0
#print axioms N11Formalization.C450Source26GroupedC09.valid1
#print axioms N11Formalization.C450Source26GroupedC09.valid2
#print axioms N11Formalization.C450Source26GroupedC09.valid3
#print axioms N11Formalization.C450Source26GroupedC09.valid4
#print axioms N11Formalization.C450Source26GroupedC09.valid5
#print axioms N11Formalization.C450Source26GroupedC09.valid6
#print axioms N11Formalization.C450Source26GroupedC09.valid7
#print axioms N11Formalization.C450Source26GroupedC09.valid8
#print axioms N11Formalization.C450Source26GroupedC09.valid9
#print axioms N11Formalization.C450Source26GroupedC09.valid10
#print axioms N11Formalization.C450Source26GroupedC09.valid11
#print axioms N11Formalization.C450Source26GroupedC09.valid12
#print axioms N11Formalization.C450Source26GroupedC09.valid13
#print axioms N11Formalization.C450Source26GroupedC09.valid14
#print axioms N11Formalization.C450Source26GroupedC09.bound
#print axioms N11Formalization.C450Source26GroupedC09.endpoint_checks
