import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/16),((-1:ℚ)/8),((1555347067:ℚ)/2500000000),((3276536963:ℚ)/5000000000),((730389111:ℚ)/51500000000),((1164652933:ℚ)/12400000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((305910281:ℚ)/500000000),((-33591028434951090561748384079540049487039793817665169009639:ℚ)/820398942968750000000000000000000000000000000000000000000000),((-774436838992430114302563:ℚ)/7220000000000000000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((6464498091:ℚ)/10000000000),((3337131021:ℚ)/5000000000),((548606937:ℚ)/52450000000),((4415501909:ℚ)/51500000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5536864867:ℚ)/10000000000),((-90531545975900552231035193195415065160797995661615634466737:ℚ)/2391833547898632812500000000000000000000000000000000000000000),((-13861254548547090351662527:ℚ)/115520000000000000000000000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((6585895419:ℚ)/10000000000),((1346964457:ℚ)/2000000000),((183106629:ℚ)/21170000000),((4294104581:ℚ)/52450000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((2612590993:ℚ)/5000000000),((-2372362355886146854574691743936211130627962827631114807492381:ℚ)/65251960976755081250000000000000000000000000000000000000000000),((-14601176301711347445944287:ℚ)/115520000000000000000000000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((6646557273:ℚ)/10000000000),((6795360817:ℚ)/10000000000),((244639183:ℚ)/35600000000),((4233442727:ℚ)/52925000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((5062954137:ℚ)/10000000000),((-150963334461526061221985340617758057383428890671782295338959:ℚ)/4328016181700000000000000000000000000000000000000000000000000),((-14972345972729801169728743:ℚ)/115520000000000000000000000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-3:ℚ)/16),((-1:ℚ)/8),((6707195497:ℚ)/10000000000),((6855878237:ℚ)/10000000000),((552365289:ℚ)/107750000000),((4172804503:ℚ)/53400000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((244795019:ℚ)/500000000),((-8089654023041610610843606966427265803656793778180516434601:ℚ)/241920071300888061523437500000000000000000000000000000000000),((-15344325550608155195976903:ℚ)/115520000000000000000000000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((845976343:ℚ)/1250000000),((3458187559:ℚ)/5000000000),((185437323:ℚ)/54350000000),((514023657:ℚ)/6734375000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4723502879:ℚ)/10000000000),((-5970632636871136192640023873227193117896118645174961242058763:ℚ)/186394547033424218750000000000000000000000000000000000000000000),((-245579967826272521601033:ℚ)/1805000000000000000000000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((170710091:ℚ)/250000000),((436053251:ℚ)/625000000),((3946749:ℚ)/2284375000),((101289909:ℚ)/1358750000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4545147693:ℚ)/10000000000),((-674717821291092397465331642010316942977989323125299122989:ℚ)/22008037130879354476928710937500000000000000000000000000000),((-10056703702440047121777:ℚ)/72200000000000000000000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((688897479:ℚ)/1000000000),((3518654731:ℚ)/5000000000),((4035807:ℚ)/55300000000),((399102521:ℚ)/5482500000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4360097729:ℚ)/10000000000),((-258700722046358687374081687664318556533939455084898069094663:ℚ)/8824908094345410156250000000000000000000000000000000000000000),((-164651521898259567537247:ℚ)/1155200000000000000000000)⟩
theorem valid7 : Valid source35 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source35 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((3474762389:ℚ)/5000000000),((7097756533:ℚ)/10000000000),((-173269599:ℚ)/110600000000),((1965237611:ℚ)/27650000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((833491019:ℚ)/2000000000),((-33809060719160343056362001497076532839901481362345695367:ℚ)/1207945550000000000000000000000000000000000000000000000000),((-11662326410600146099887:ℚ)/80000000000000000000000)⟩
theorem valid8 : Valid source35 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((1402010833:ℚ)/2000000000),((3579101793:ℚ)/5000000000),((-177305379:ℚ)/55775000000),((773989167:ℚ)/11155000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3966107229:ℚ)/10000000000),((-1258489552228312666953049817394760682653108411818226827:ℚ)/47148829785156250000000000000000000000000000000000000000),((-688658794295610824863863:ℚ)/4620800000000000000000000)⟩
theorem valid9 : Valid source35 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source35 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source35 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((3535281747:ℚ)/5000000000),((727909603:ℚ)/1000000000),((-23909603:ℚ)/3750000000),((1904718253:ℚ)/28125000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3754647351:ℚ)/10000000000),((-7948954041275015926304490074702524812030361274147077:ℚ)/329589843750000000000000000000000000000000000000000000),((-4398341541712792322116903:ℚ)/28880000000000000000000000)⟩
theorem valid10 : Valid source35 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((7191524049:ℚ)/10000000000),((7520712717:ℚ)/10000000000),((-1442138151:ℚ)/114400000000),((3688475951:ℚ)/57200000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((164674393:ℚ)/500000000),((-44807177685903497171014318903925562750111645206301149409:ℚ)/2339365600000000000000000000000000000000000000000000000000),((-18349645354050963198304567:ℚ)/115520000000000000000000000)⟩
theorem valid11 : Valid source35 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((1486645259:ℚ)/2000000000),((7762066673:ℚ)/10000000000),((-722066673:ℚ)/39400000000),((689354741:ℚ)/11820000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2098791911:ℚ)/10000000000),((-5626969198605123835574625245283053403731640443124725823:ℚ)/382268650000000000000000000000000000000000000000000000000),((-794888409575454454520127:ℚ)/4620800000000000000000000)⟩
theorem valid12 : Valid source35 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source35 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((959332527:ℚ)/1250000000),((4122040807:ℚ)/5000000000),((-1806122421:ℚ)/61000000000),((400667473:ℚ)/7625000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-2134900496476749275854568124489656537225217679898040459:ℚ)/354657812500000000000000000000000000000000000000000000000),((-927717:ℚ)/5120000)⟩
theorem valid13 : Valid source35 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((8156820391:ℚ)/10000000000),((2541342393:ℚ)/2500000000),((-781342393:ℚ)/10800000000),((2723179609:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((4288358237527632973519210476249250309008586119307411:ℚ)/164025000000000000000000000000000000000000000000000000),((-927717:ℚ)/5120000)⟩
theorem valid14 : Valid source35 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((10078546813:ℚ)/10000000000),((13990189299:ℚ)/10000000000),((-20850567897:ℚ)/160000000000),((801453187:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((78117935782186452387601604852205578931:ℚ)/1024000000000000000000000000000000000000),((-927717:ℚ)/5120000)⟩
theorem valid15 : Valid source35 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source35 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC14
#check @N11Formalization.C450Source35GroupedC14.bound
#print axioms N11Formalization.C450Source35GroupedC14.valid0
#print axioms N11Formalization.C450Source35GroupedC14.valid1
#print axioms N11Formalization.C450Source35GroupedC14.valid2
#print axioms N11Formalization.C450Source35GroupedC14.valid3
#print axioms N11Formalization.C450Source35GroupedC14.valid4
#print axioms N11Formalization.C450Source35GroupedC14.valid5
#print axioms N11Formalization.C450Source35GroupedC14.valid6
#print axioms N11Formalization.C450Source35GroupedC14.valid7
#print axioms N11Formalization.C450Source35GroupedC14.valid8
#print axioms N11Formalization.C450Source35GroupedC14.valid9
#print axioms N11Formalization.C450Source35GroupedC14.valid10
#print axioms N11Formalization.C450Source35GroupedC14.valid11
#print axioms N11Formalization.C450Source35GroupedC14.valid12
#print axioms N11Formalization.C450Source35GroupedC14.valid13
#print axioms N11Formalization.C450Source35GroupedC14.valid14
#print axioms N11Formalization.C450Source35GroupedC14.valid15
#print axioms N11Formalization.C450Source35GroupedC14.bound
#print axioms N11Formalization.C450Source35GroupedC14.endpoint_checks
