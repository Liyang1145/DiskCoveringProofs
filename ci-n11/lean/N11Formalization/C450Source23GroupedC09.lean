import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((1304263279:ℚ)/2000000000),((6832230149:ℚ)/10000000000),((-5152230149:ℚ)/12400000000),((-6313842953:ℚ)/20600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((215720327:ℚ)/400000000),((83278847435580039017291859170745551939274753624525794991:ℚ)/423431712500000000000000000000000000000000000000000000000),((8980387626423926856542361:ℚ)/73932800000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((6760532337:ℚ)/10000000000),((1737951437:ℚ)/2500000000),((-1317951437:ℚ)/3218750000),((-33243726359:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2372254321:ℚ)/5000000000),((8887224394061991146792217041239064168211459592656307542049:ℚ)/46443369862109375000000000000000000000000000000000000000000),((624585829265491462889428747:ℚ)/5544960000000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((6880093207:ℚ)/10000000000),((7011582319:ℚ)/10000000000),((-5331582319:ℚ)/13112500000),((-34080652449:ℚ)/105850000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((877537469:ℚ)/2000000000),((367116683971361720974483772993486898544690839837967532203393:ℚ)/1943873956647851562500000000000000000000000000000000000000000),((199957737436784062825701129:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((867482827:ℚ)/1250000000),((282854067:ℚ)/400000000),((-215654067:ℚ)/529250000),((-4312379789:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((131211003:ℚ)/312500000),((123788748771358216856381474077071902019857938430161539803:ℚ)/655848357275390625000000000000000000000000000000000000000),((3059669565664638668165809:ℚ)/28880000000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/2),((-7:ℚ)/16),((349981247:ℚ)/500000000),((891389251:ℚ)/1250000000),((-7656059:ℚ)/18750000),((-1745868729:ℚ)/5387500000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4001481759:ℚ)/10000000000),((540123056048834069668327988293476613424829028681411:ℚ)/2863275682926177978515625000000000000000000000000000),((479166362074679595146489:ℚ)/4620800000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((441211273:ℚ)/625000000),((7190869507:ℚ)/10000000000),((-5510869507:ℚ)/13468750000),((-2208478911:ℚ)/6793750000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((948642977:ℚ)/2500000000),((39812279813872289006107323438838786449610672299280656913:ℚ)/211166966168594360351562500000000000000000000000000000000),((732425027612945966926409:ℚ)/7220000000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((7119129083:ℚ)/10000000000),((7250618349:ℚ)/10000000000),((-5570618349:ℚ)/13587500000),((-35753903581:ℚ)/109650000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((447043119:ℚ)/1250000000),((689423315065945283561423413433994123830013908365885956547:ℚ)/3658676880029296875000000000000000000000000000000000000000),((183321630913629351940725969:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((7178871263:ℚ)/10000000000),((731036071:ℚ)/1000000000),((-563036071:ℚ)/1370625000),((-36172098841:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((836145303:ℚ)/2500000000),((13642243157053329999283978063524502158997335514190918231281:ℚ)/72434266164257812500000000000000000000000000000000000000000),((179129008538559552501201849:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((7238607077:ℚ)/10000000000),((1842524189:ℚ)/2500000000),((-1422524189:ℚ)/3456250000),((-36590249539:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((619247377:ℚ)/2000000000),((14111203514595538606324358665734534226952032256426362836979:ℚ)/74960745754675292968750000000000000000000000000000000000000),((174922932586798458634577809:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/2),((-7:ℚ)/16),((7298336691:ℚ)/10000000000),((148596533:ℚ)/200000000),((-114996533:ℚ)/278875000),((-37008356837:ℚ)/112500000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2826939653:ℚ)/10000000000),((3648077753575340922891385208539437352187927456094354814739:ℚ)/19388186931610107421875000000000000000000000000000000000000),((512110187267831752825722403:ℚ)/5544960000000000000000000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((3679030131:ℚ)/5000000000),((7549268601:ℚ)/10000000000),((-1956422867:ℚ)/4687500000),((-18713210917:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2530001077:ℚ)/10000000000),((15159086913998864875916136533106852873375600977387229517:ℚ)/79751100000000000000000000000000000000000000000000000000),((124852793420689826306254243:ℚ)/1386240000000000000000000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((233671559:ℚ)/312500000),((1947021303:ℚ)/2500000000),((-1527021303:ℚ)/3575000000),((-398566971:ℚ)/1231250000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1797956979:ℚ)/10000000000),((20199207988155611637956570629498017139825056230663229:ℚ)/104264100933074951171875000000000000000000000000000000),((154261672015608184821801:ℚ)/1805000000000000000000000)⟩
theorem valid11 : Valid source23 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/2),((-7:ℚ)/16),((385814153:ℚ)/500000000),((1605363833:ℚ)/2000000000),((-1269363833:ℚ)/2955000000),((-1996699071:ℚ)/6100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((40496237744374961686428259075771280237122974561779191553:ℚ)/209602767187500000000000000000000000000000000000000000000),((10331051:ℚ)/128000000)⟩
theorem valid12 : Valid source23 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source23 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((1590999011:ℚ)/2000000000),((1700813691:ℚ)/2000000000),((-1364813691:ℚ)/3050000000),((-2773664359:ℚ)/8640000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1363509347254295582776106889675866656267020488626217843:ℚ)/6830438400000000000000000000000000000000000000000000000),((10331051:ℚ)/128000000)⟩
theorem valid13 : Valid source23 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((8432204347:ℚ)/10000000000),((5205458857:ℚ)/5000000000),((-4365458857:ℚ)/8100000000),((-44945430429:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((120769968066723658069680958598658554757782989419985097186717:ℚ)/518400000000000000000000000000000000000000000000000000000000),((10331051:ℚ)/128000000)⟩
theorem valid14 : Valid source23 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((10338932003:ℚ)/10000000000),((2843788091:ℚ)/2000000000),((-2507788091:ℚ)/4000000000),((-58292524021:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1128740128857704975046097115797671330593068991489595260333:ℚ)/4204915200000000000000000000000000000000000000000000000000),((10331051:ℚ)/128000000)⟩
theorem valid15 : Valid source23 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source23 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source23 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC09
#check @N11Formalization.C450Source23GroupedC09.bound
#print axioms N11Formalization.C450Source23GroupedC09.valid0
#print axioms N11Formalization.C450Source23GroupedC09.valid1
#print axioms N11Formalization.C450Source23GroupedC09.valid2
#print axioms N11Formalization.C450Source23GroupedC09.valid3
#print axioms N11Formalization.C450Source23GroupedC09.valid4
#print axioms N11Formalization.C450Source23GroupedC09.valid5
#print axioms N11Formalization.C450Source23GroupedC09.valid6
#print axioms N11Formalization.C450Source23GroupedC09.valid7
#print axioms N11Formalization.C450Source23GroupedC09.valid8
#print axioms N11Formalization.C450Source23GroupedC09.valid9
#print axioms N11Formalization.C450Source23GroupedC09.valid10
#print axioms N11Formalization.C450Source23GroupedC09.valid11
#print axioms N11Formalization.C450Source23GroupedC09.valid12
#print axioms N11Formalization.C450Source23GroupedC09.valid13
#print axioms N11Formalization.C450Source23GroupedC09.valid14
#print axioms N11Formalization.C450Source23GroupedC09.valid15
#print axioms N11Formalization.C450Source23GroupedC09.bound
#print axioms N11Formalization.C450Source23GroupedC09.endpoint_checks
