import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((6443623531:ℚ)/10000000000),((841978491:ℚ)/1250000000),((-6537806419:ℚ)/12400000000),((-5323623531:ℚ)/12875000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2794440611:ℚ)/5000000000),((22036839458292797522391924920286951334136018658818082579:ℚ)/413507531738281250000000000000000000000000000000000000000),((2847385094535647014246531243:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((6681729223:ℚ)/10000000000),((856860083:ℚ)/1250000000),((-6671740747:ℚ)/12875000000),((-5561729223:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((993336989:ℚ)/2000000000),((18710146152574888283890550002548083000054717168887731111:ℚ)/362838827047729492187500000000000000000000000000000000000),((2823120072643343582350958227:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((3400382777:ℚ)/5000000000),((1743480647:ℚ)/2500000000),((-13611325823:ℚ)/26225000000),((-946794259:ℚ)/2225000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4627291237:ℚ)/10000000000),((930863913630136936528528434302984507857498858359221149:ℚ)/18054503930664062500000000000000000000000000000000000000),((702739209957724431401582227:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-9:ℚ)/16),((-1:ℚ)/2),((6919791661:ℚ)/10000000000),((1758359919:ℚ)/2500000000),((-13745239271:ℚ)/26700000000),((-5799791661:ℚ)/13468750000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1065768401:ℚ)/2500000000),((808560091746500656858224268548985019522497235369784913:ℚ)/15926970986276865005493164062500000000000000000000000000),((2798773053238200636244273723:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((139586021:ℚ)/200000000),((7092954271:ℚ)/10000000000),((-55516588439:ℚ)/107750000000),((-117186021:ℚ)/271750000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4069581559:ℚ)/10000000000),((2744685048614939076732205994069102263531985224515029:ℚ)/54058743339160156250000000000000000000000000000000000),((1117069374652932068809483:ℚ)/5914624000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7038808083:ℚ)/10000000000),((7152466439:ℚ)/10000000000),((-56052197951:ℚ)/108700000000),((-5918808083:ℚ)/13706250000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((120843489:ℚ)/312500000),((8224526609886201401806606162170271297456337073620300233:ℚ)/161972674376296997070312500000000000000000000000000000000),((2786568663110776375660613307:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-9:ℚ)/16),((-1:ℚ)/2),((7098312821:ℚ)/10000000000),((112222213:ℚ)/156250000),((-51764701:ℚ)/100781250),((-5978312821:ℚ)/13765625000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((1826893339:ℚ)/5000000000),((26499808244049395122994639272850645003493313200123171179:ℚ)/525772103601694107055664062500000000000000000000000000000),((2780458727048490411536962283:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((7128064347:ℚ)/10000000000),((3605988121:ℚ)/5000000000),((-28293893089:ℚ)/55062500000),((-6008064347:ℚ)/13825000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((885651769:ℚ)/2500000000),((11459224349383275245548497515429738892150764690653400493:ℚ)/227337652796936035156250000000000000000000000000000000000),((2777401821448418702765213067:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((3578907661:ℚ)/5000000000),((1810432569:ℚ)/2500000000),((-14213893121:ℚ)/27650000000),((-3018907661:ℚ)/6942187500),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((685596441:ℚ)/2000000000),((4857737272256261512766877900142121201542196999870683349:ℚ)/96363578732353448867797851562500000000000000000000000000),((693585905776678130333849723:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((898445719:ℚ)/1250000000),((3635741871:ℚ)/5000000000),((-28561676839:ℚ)/55537500000),((-758445719:ℚ)/1742968750),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((66191071:ℚ)/200000000),((231649902667568147158325012816942295853850965645650701:ℚ)/4594890372195560485124588012695312500000000000000000000),((43301314554393367661528243:ℚ)/231040000000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-9:ℚ)/16),((-1:ℚ)/2),((1443463129:ℚ)/2000000000),((1832747249:ℚ)/2500000000),((-14414725241:ℚ)/27887500000),((-1219463129:ℚ)/2812500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6373793:ℚ)/20000000),((20514693670168461260407629668623427553431563238829467:ℚ)/403920561075210571289062500000000000000000000000000000),((110728933832908333526016083:ℚ)/591462400000000000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((1819203461:ℚ)/2500000000),((3695246031:ℚ)/5000000000),((-29097214279:ℚ)/56250000000),((-1539203461:ℚ)/3545312500),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((365843837:ℚ)/1250000000),((318287534585692809856552590539116755335194219069559:ℚ)/6266515253841876983642578125000000000000000000000000),((172631118139206320659288523:ℚ)/924160000000000000000000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((293452399:ℚ)/400000000),((1489998599:ℚ)/2000000000),((-11745987391:ℚ)/22690000000),((-248652399:ℚ)/572000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2641914811:ℚ)/10000000000),((134808213570205895637997946616726000174624939989032989:ℚ)/2654010273200000000000000000000000000000000000000000000),((4409547601800840368155363:ℚ)/23658496000000000000000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((7395804087:ℚ)/10000000000),((1892247167:ℚ)/2500000000),((-14950224503:ℚ)/28600000000),((-6275804087:ℚ)/14537500000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((580829867:ℚ)/2500000000),((141420980398215955495089500046114464370916183500738724679:ℚ)/2745903293713378906250000000000000000000000000000000000000),((2749831424024329076721276147:ℚ)/14786560000000000000000000000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((939348307:ℚ)/1250000000),((384398821:ℚ)/500000000),((-3043589389:ℚ)/5815000000),((-799348307:ℚ)/1846875000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1498887853:ℚ)/10000000000),((21830020734002382502859938663767629469364474798259213:ℚ)/423983039808273315429687500000000000000000000000000000),((42774127924098948905660987:ℚ)/231040000000000000000000000)⟩
theorem valid14 : Valid source15 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-9:ℚ)/16),((-1:ℚ)/2),((3816880667:ℚ)/5000000000),((7925929643:ℚ)/10000000000),((-63013366787:ℚ)/118200000000),((-3256880667:ℚ)/7625000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((86454159250180693335288737783359611556954249897925891707:ℚ)/1637521618652343750000000000000000000000000000000000000000),((188970289:ℚ)/1024000000)⟩
theorem valid15 : Valid source15 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((393584501:ℚ)/500000000),((8401756151:ℚ)/10000000000),((-67295805359:ℚ)/122000000000),((-37509389:ℚ)/90000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1703136089533846026355605335243418105195918465839:ℚ)/30881250000000000000000000000000000000000000000000),((188970289:ℚ)/1024000000)⟩
theorem valid16 : Valid source15 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((834747179:ℚ)/1000000000),((5152137751:ℚ)/5000000000),((-42209239759:ℚ)/64800000000),((-722747179:ℚ)/2000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((38202281169241581486024249267478907596313964846553082987:ℚ)/566870400000000000000000000000000000000000000000000000000),((188970289:ℚ)/1024000000)⟩
theorem valid17 : Valid source15 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((10249854851:ℚ)/10000000000),((2821446121:ℚ)/2000000000),((-23729015089:ℚ)/32000000000),((-9129854851:ℚ)/27600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((19763781701648325655757033878367264902223369974811381235311:ℚ)/243763200000000000000000000000000000000000000000000000000000),((188970289:ℚ)/1024000000)⟩
theorem valid18 : Valid source15 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source15 nn0 nn1 Qcell ((1049:ℚ)/1600) ((431:ℚ)/640) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source15 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source15 nn0 nn1 Qcell ((881:ℚ)/1280) ((4443:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source15 nn0 nn1 Qcell ((2193:ℚ)/3200) ((4443:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source15 nn0 nn1 Qcell ((431:ℚ)/640) ((4443:ℚ)/6400) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((4443:ℚ)/6400) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source15 nn0 nn1 Qcell ((4443:ℚ)/6400) ((45:ℚ)/64) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source15 nn0 nn1 Qcell ((4443:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source15 nn0 nn1 Qcell ((4443:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC08
#check @N11Formalization.C450Source15GroupedC08.bound
#print axioms N11Formalization.C450Source15GroupedC08.valid0
#print axioms N11Formalization.C450Source15GroupedC08.valid1
#print axioms N11Formalization.C450Source15GroupedC08.valid2
#print axioms N11Formalization.C450Source15GroupedC08.valid3
#print axioms N11Formalization.C450Source15GroupedC08.valid4
#print axioms N11Formalization.C450Source15GroupedC08.valid5
#print axioms N11Formalization.C450Source15GroupedC08.valid6
#print axioms N11Formalization.C450Source15GroupedC08.valid7
#print axioms N11Formalization.C450Source15GroupedC08.valid8
#print axioms N11Formalization.C450Source15GroupedC08.valid9
#print axioms N11Formalization.C450Source15GroupedC08.valid10
#print axioms N11Formalization.C450Source15GroupedC08.valid11
#print axioms N11Formalization.C450Source15GroupedC08.valid12
#print axioms N11Formalization.C450Source15GroupedC08.valid13
#print axioms N11Formalization.C450Source15GroupedC08.valid14
#print axioms N11Formalization.C450Source15GroupedC08.valid15
#print axioms N11Formalization.C450Source15GroupedC08.valid16
#print axioms N11Formalization.C450Source15GroupedC08.valid17
#print axioms N11Formalization.C450Source15GroupedC08.valid18
#print axioms N11Formalization.C450Source15GroupedC08.bound
#print axioms N11Formalization.C450Source15GroupedC08.endpoint_checks
