import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((6602234411:ℚ)/10000000000),((345561593:ℚ)/500000000),((-3257177523:ℚ)/4960000000),((-5450234411:ℚ)/10300000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1295485381:ℚ)/2500000000),((625030911971415173562968445548609350257527680444398154209:ℚ)/8090949606400000000000000000000000000000000000000000000000),((2665932184825246675579225063:ℚ)/7393280000000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((427536077:ℚ)/625000000),((7030368321:ℚ)/10000000000),((-66454051531:ℚ)/103000000000),((-355536077:ℚ)/655625000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2254262679:ℚ)/5000000000),((138010534412286191155013224132740651592544737007517471181042097:ℚ)/1878809193010937500000000000000000000000000000000000000000000000),((10381823910608698078330487:ℚ)/28880000000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((1739931407:ℚ)/2500000000),((1772482831:ℚ)/2500000000),((-16777311141:ℚ)/26225000000),((-1451931407:ℚ)/2646250000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4134171277:ℚ)/10000000000),((496022023050871828591970299786642319568770804493723494752359:ℚ)/6920625742583691406250000000000000000000000000000000000000000),((165848930041002832689955647:ℚ)/462080000000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((1754823609:ℚ)/2500000000),((7149490967:ℚ)/10000000000),((-67764400637:ℚ)/105850000000),((-488941203:ℚ)/890000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((786902791:ℚ)/2000000000),((14425165807065915410876326025581680988527611425349229198983:ℚ)/201071152050976562500000000000000000000000000000000000000000),((497153063166437975235690829:ℚ)/1386240000000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((353942989:ℚ)/500000000),((7179269557:ℚ)/10000000000),((-22697321709:ℚ)/35600000000),((-296342989:ℚ)/536375000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((744953157:ℚ)/2000000000),((5750642354548971501520564449893766882562133186186383192879047:ℚ)/81127308199306250000000000000000000000000000000000000000000000),((6623428050439235003196663:ℚ)/18483200000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-11:ℚ)/16),((-5:ℚ)/8),((7108641181:ℚ)/10000000000),((7209047339:ℚ)/10000000000),((-9774217247:ℚ)/15325000000),((-5956641181:ℚ)/10775000000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1807780403:ℚ)/5000000000),((3472914034899954879332546017851650179234905327986425542887:ℚ)/48968555892696762084960937500000000000000000000000000000000),((2648310863289952132738170583:ℚ)/7393280000000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7138421751:ℚ)/10000000000),((3619412163:ℚ)/5000000000),((-34373533793:ℚ)/53875000000),((-1995473917:ℚ)/3607500000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((3503110187:ℚ)/10000000000),((3008374592729613435110426252265597164946439082269608981069697:ℚ)/42396820817758941650390625000000000000000000000000000000000000),((7941742588094315999743468909:ℚ)/22179840000000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((14336403:ℚ)/20000000),((7268600527:ℚ)/10000000000),((-23024868599:ℚ)/36075000000),((-12032403:ℚ)/21740000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1693545057:ℚ)/5000000000),((221743139338191792211619006060048479988342717612688328261603:ℚ)/3123454227817675781250000000000000000000000000000000000000000),((31754174619519253599781:ℚ)/88719360000000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7197980439:ℚ)/10000000000),((456148497:ℚ)/625000000),((-4337633467:ℚ)/6793750000),((-6045980439:ℚ)/10917500000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((3267119751:ℚ)/10000000000),((165913304993748296342894544370293038643767418690797013224961:ℚ)/2335904604915768337249755859375000000000000000000000000000000),((7935335789785691797590137389:ℚ)/22179840000000000000000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7227758579:ℚ)/10000000000),((7328150613:ℚ)/10000000000),((-69729656743:ℚ)/109175000000),((-6075758579:ℚ)/10965000000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((314274613:ℚ)/1000000000),((231620797081176815577453338297049055517450019126620090311940623:ℚ)/3259459854941275122070312500000000000000000000000000000000000000),((2644039664119316157640828023:ℚ)/7393280000000000000000000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((725753593:ℚ)/1000000000),((3693848839:ℚ)/5000000000),((-35192337229:ℚ)/54825000000),((-610553593:ℚ)/1106000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3013423463:ℚ)/10000000000),((1062763299460393422991029688721348751071867160369714400743901:ℚ)/14764117121787016296386718750000000000000000000000000000000000),((26429644207459051395185647:ℚ)/73932800000000000000000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((3658544153:ℚ)/5000000000),((37236209:ℚ)/50000000),((-4496181:ℚ)/7000000),((-3082544153:ℚ)/5577500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((547419373:ℚ)/2000000000),((6862801855116464714290752582175032299887699820841:ℚ)/95269800390625000000000000000000000000000000000000),((660201250192879959043626927:ℚ)/1848320000000000000000000000)⟩
theorem valid11 : Valid source19 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-11:ℚ)/16),((-5:ℚ)/8),((7376637647:ℚ)/10000000000),((3753391527:ℚ)/5000000000),((-35847306797:ℚ)/55775000000),((-6224637647:ℚ)/11250000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((151901701:ℚ)/625000000),((8244574677111946019952803735483767076456473786568616493:ℚ)/114372747252273559570312500000000000000000000000000000000),((2638633668966940481337614527:ℚ)/7393280000000000000000000000)⟩
theorem valid12 : Valid source19 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source19 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source19 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((232380751:ℚ)/312500000),((1906464311:ℚ)/2500000000),((-18251107421:ℚ)/28125000000),((-196380751:ℚ)/357500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2080029581:ℚ)/10000000000),((209947088951664668648306172059725559697377396729637819773327:ℚ)/2843345832824707031250000000000000000000000000000000000000000),((2574658617447040471810303:ℚ)/7220000000000000000000000)⟩
theorem valid13 : Valid source19 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-11:ℚ)/16),((-5:ℚ)/8),((302210729:ℚ)/400000000),((8102052651:ℚ)/10000000000),((-78242579161:ℚ)/114400000000),((-256130729:ℚ)/488000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((108549921:ℚ)/1000000000),((8740741224994131346802735463546215953488702067374287125217089:ℚ)/104457352771200000000000000000000000000000000000000000000000000),((4211277108028640339924623:ℚ)/11829248000000000000000000)⟩
theorem valid14 : Valid source19 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source19 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((8031500507:ℚ)/10000000000),((2144526847:ℚ)/2500000000),((-20869795317:ℚ)/30500000000),((-6879500507:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((32191312939024052736157782982828581534842455324020285381173:ℚ)/387818317968750000000000000000000000000000000000000000000000),((182159429:ℚ)/512000000)⟩
theorem valid15 : Valid source19 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((2126896941:ℚ)/2500000000),((5240660949:ℚ)/5000000000),((-52207270439:ℚ)/64800000000),((-1838896941:ℚ)/4000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((588177165055026689532246763735707927668251164135815144111:ℚ)/5101833600000000000000000000000000000000000000000000000000),((182159429:ℚ)/512000000)⟩
theorem valid16 : Valid source19 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((10410901309:ℚ)/10000000000),((7142545777:ℚ)/5000000000),((-73128003547:ℚ)/80000000000),((-9258901309:ℚ)/22080000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((30595185171793812799080969362154248333689:ℚ)/203136000000000000000000000000000000000000),((182159429:ℚ)/512000000)⟩
theorem valid17 : Valid source19 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source19 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source19 nn0 nn1 Qcell ((4329:ℚ)/6400) ((4367:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source19 nn0 nn1 Qcell ((431:ℚ)/640) ((4367:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((4367:ℚ)/6400) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((4367:ℚ)/6400) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source19 nn0 nn1 Qcell ((4367:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source19 nn0 nn1 Qcell ((4367:ℚ)/6400) ((45:ℚ)/64) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((61:ℚ)/80) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound source19 nn0 nn1 Qcell ((4367:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC06
#check @N11Formalization.C450Source19GroupedC06.bound
#print axioms N11Formalization.C450Source19GroupedC06.valid0
#print axioms N11Formalization.C450Source19GroupedC06.valid1
#print axioms N11Formalization.C450Source19GroupedC06.valid2
#print axioms N11Formalization.C450Source19GroupedC06.valid3
#print axioms N11Formalization.C450Source19GroupedC06.valid4
#print axioms N11Formalization.C450Source19GroupedC06.valid5
#print axioms N11Formalization.C450Source19GroupedC06.valid6
#print axioms N11Formalization.C450Source19GroupedC06.valid7
#print axioms N11Formalization.C450Source19GroupedC06.valid8
#print axioms N11Formalization.C450Source19GroupedC06.valid9
#print axioms N11Formalization.C450Source19GroupedC06.valid10
#print axioms N11Formalization.C450Source19GroupedC06.valid11
#print axioms N11Formalization.C450Source19GroupedC06.valid12
#print axioms N11Formalization.C450Source19GroupedC06.valid13
#print axioms N11Formalization.C450Source19GroupedC06.valid14
#print axioms N11Formalization.C450Source19GroupedC06.valid15
#print axioms N11Formalization.C450Source19GroupedC06.valid16
#print axioms N11Formalization.C450Source19GroupedC06.valid17
#print axioms N11Formalization.C450Source19GroupedC06.bound
#print axioms N11Formalization.C450Source19GroupedC06.endpoint_checks
