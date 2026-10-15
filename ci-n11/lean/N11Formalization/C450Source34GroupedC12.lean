import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((6394866251:ℚ)/10000000000),((6605589523:ℚ)/10000000000),((-2509589523:ℚ)/19840000000),((-1114866251:ℚ)/25275000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((2854363019:ℚ)/5000000000),((3615119426892543902078345285813362329:ℚ)/48809574400000000000000000000000000000),((-2263142050398512852547259:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((1629003743:ℚ)/2500000000),((3363351619:ℚ)/5000000000),((-1315351619:ℚ)/10110000000),((-309003743:ℚ)/6437500000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((2703288089:ℚ)/5000000000),((30786046695156215408176025154865550871519030787869467:ℚ)/403657941796875000000000000000000000000000000000000000),((-246214538853336193935691:ℚ)/14440000000000000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((6637072599:ℚ)/10000000000),((6787226743:ℚ)/10000000000),((-2691226743:ℚ)/20600000000),((-452357533:ℚ)/8662500000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((1272157371:ℚ)/2500000000),((16249341525919274532116481062952190792814326880355639:ℚ)/213423242187500000000000000000000000000000000000000000),((-16885222698033246288426377:ℚ)/693120000000000000000000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((6697568873:ℚ)/10000000000),((6847728849:ℚ)/10000000000),((-2751728849:ℚ)/20790000000),((-1417568873:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((4922767777:ℚ)/10000000000),((18765331574096638750993110815158628004022080783114407:ℚ)/243126056250000000000000000000000000000000000000000000),((-6477664642450727932761411:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((6758044271:ℚ)/10000000000),((1381642031:ℚ)/2000000000),((-562442031:ℚ)/4196000000),((-1478044271:ℚ)/26462500000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((950333923:ℚ)/2000000000),((36110824986360401335900627468713137026225085634309687:ℚ)/461728259600000000000000000000000000000000000000000000),((-7330108001173072372775219:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((3409249687:ℚ)/5000000000),((6968671237:ℚ)/10000000000),((-2872671237:ℚ)/21170000000),((-769249687:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((228737091:ℚ)/500000000),((1174269040982293566412650936017850975298366426829617629:ℚ)/14824586895312500000000000000000000000000000000000000000),((-2046435569833833189221971:ℚ)/57760000000000000000000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-5:ℚ)/16),((-1:ℚ)/4),((6878934743:ℚ)/10000000000),((7029112647:ℚ)/10000000000),((-2933112647:ℚ)/21360000000),((-1598934743:ℚ)/26937500000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2195637013:ℚ)/5000000000),((14653563720778127603174967037150994069871216991395733237:ℚ)/182727964800000000000000000000000000000000000000000000000),((-25054215967154924683531:ℚ)/640000000000000000000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((173483773:ℚ)/250000000),((3544767461:ℚ)/5000000000),((-1496767461:ℚ)/10775000000),((-41483773:ℚ)/679375000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1050100857:ℚ)/2500000000),((634531159891040378280010948256675050660660887940369317:ℚ)/7818651464843750000000000000000000000000000000000000000),((-6191625875805718652511:ℚ)/144400000000000000000000)⟩
theorem valid7 : Valid source34 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source34 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/16),((-1:ℚ)/4),((3499874213:ℚ)/5000000000),((285997543:ℚ)/400000000),((-122157543:ℚ)/869600000),((-859874213:ℚ)/13706250000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4001064643:ℚ)/10000000000),((21089286378883095726351889552784756534763250638639:ℚ)/256873100600000000000000000000000000000000000000000),((-2692958690171234673314571:ℚ)/57760000000000000000000000)⟩
theorem valid8 : Valid source34 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((7060127761:ℚ)/10000000000),((7210324103:ℚ)/10000000000),((-3114324103:ℚ)/21930000000),((-1780127761:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3791916141:ℚ)/10000000000),((127274416389198749994545735533831018578975820224999037:ℚ)/1532948118750000000000000000000000000000000000000000000),((-11640276030330982556820339:ℚ)/231040000000000000000000000)⟩
theorem valid9 : Valid source34 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source34 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((712048941:ℚ)/1000000000),((3665521341:ℚ)/5000000000),((-1617521341:ℚ)/11060000000),((-61349647:ℚ)/937500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((714245661:ℚ)/2000000000),((103824181858460357666170487454776277661990878423363611:ℚ)/1207945550000000000000000000000000000000000000000000000),((-375357872910396220746737:ℚ)/6931200000000000000000000)⟩
theorem valid10 : Valid source34 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source34 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((7241161501:ℚ)/10000000000),((1862923573:ℚ)/2500000000),((-279641191:ℚ)/1875000000),((-150858577:ℚ)/2200000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((308518701:ℚ)/1000000000),((3611968395875809569663194433878667826707620490391567:ℚ)/41198730468750000000000000000000000000000000000000000),((-14264885432045232370049259:ℚ)/231040000000000000000000000)⟩
theorem valid11 : Valid source34 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((7361768241:ℚ)/10000000000),((7933695469:ℚ)/10000000000),((-3837695469:ℚ)/22880000000),((-2081768241:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((2510435497:ℚ)/10000000000),((1886515812339170269152410174114716610959632885574250037:ℚ)/18714924800000000000000000000000000000000000000000000000),((-48092196317176476360886937:ℚ)/693120000000000000000000000)⟩
theorem valid12 : Valid source34 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source34 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((7843604519:ℚ)/10000000000),((420742971:ℚ)/500000000),((-215942971:ℚ)/1220000000),((-2563604519:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((300770613882322028805022877673411582526660787074643:ℚ)/2837262500000000000000000000000000000000000000000000),((-10836247:ℚ)/128000000)⟩
theorem valid13 : Valid source34 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((8324623661:ℚ)/10000000000),((645848523:ℚ)/625000000),((-389848523:ℚ)/1620000000),((-3044623661:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((741537950511453113753220821044571249130930624701137:ℚ)/4982259375000000000000000000000000000000000000000000),((-10836247:ℚ)/128000000)⟩
theorem valid14 : Valid source34 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((10242902799:ℚ)/10000000000),((14155416587:ℚ)/10000000000),((-10059416587:ℚ)/32000000000),((-1654300933:ℚ)/18400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((344570475885669053472594353293061877:ℚ)/1638400000000000000000000000000000000),((-10836247:ℚ)/128000000)⟩
theorem valid15 : Valid source34 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source34 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source34 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC12
#check @N11Formalization.C450Source34GroupedC12.bound
#print axioms N11Formalization.C450Source34GroupedC12.valid0
#print axioms N11Formalization.C450Source34GroupedC12.valid1
#print axioms N11Formalization.C450Source34GroupedC12.valid2
#print axioms N11Formalization.C450Source34GroupedC12.valid3
#print axioms N11Formalization.C450Source34GroupedC12.valid4
#print axioms N11Formalization.C450Source34GroupedC12.valid5
#print axioms N11Formalization.C450Source34GroupedC12.valid6
#print axioms N11Formalization.C450Source34GroupedC12.valid7
#print axioms N11Formalization.C450Source34GroupedC12.valid8
#print axioms N11Formalization.C450Source34GroupedC12.valid9
#print axioms N11Formalization.C450Source34GroupedC12.valid10
#print axioms N11Formalization.C450Source34GroupedC12.valid11
#print axioms N11Formalization.C450Source34GroupedC12.valid12
#print axioms N11Formalization.C450Source34GroupedC12.valid13
#print axioms N11Formalization.C450Source34GroupedC12.valid14
#print axioms N11Formalization.C450Source34GroupedC12.valid15
#print axioms N11Formalization.C450Source34GroupedC12.bound
#print axioms N11Formalization.C450Source34GroupedC12.endpoint_checks
