import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((3267284753:ℚ)/5000000000),((6835237931:ℚ)/10000000000),((-66227617241:ℚ)/99200000000),((-2787284753:ℚ)/5150000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2679476959:ℚ)/5000000000),((148865251283122629298751430578127593819827461039163316152589:ℚ)/2427284881920000000000000000000000000000000000000000000000000),((3056865973611088236530869:ℚ)/10240000000000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((52911251:ℚ)/78125000),((6954255907:ℚ)/10000000000),((-67536814977:ℚ)/103000000000),((-45411251:ℚ)/81953125),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((588689663:ℚ)/1250000000),((1373430169015109540857639401472313757039208770653480965522879:ℚ)/23485114912636718750000000000000000000000000000000000000000000),((14156544698726731190279:ℚ)/47500000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((6891659883:ℚ)/10000000000),((280550451:ℚ)/400000000),((-2727654961:ℚ)/4196000000),((-5931659883:ℚ)/10585000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4351724587:ℚ)/10000000000),((20246949932078796062234080964815714665377356749309626711:ℚ)/354336038020285000000000000000000000000000000000000000000),((695243679170672889071602693:ℚ)/2334720000000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((6951166117:ℚ)/10000000000),((7073264317:ℚ)/10000000000),((-68845907487:ℚ)/105850000000),((-5991166117:ℚ)/10680000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((208105829:ℚ)/500000000),((143699974030952624053880387517015490532478015456206887537:ℚ)/2513389400637207031250000000000000000000000000000000000000),((231650814584667825252770231:ℚ)/778240000000000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7010670009:ℚ)/10000000000),((887876873:ℚ)/1250000000),((-2882215201:ℚ)/4450000000),((-6050670009:ℚ)/10727500000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((1982004513:ℚ)/5000000000),((111964947423937818111948674601030015705031716883424272927:ℚ)/1980647172834625244140625000000000000000000000000000000000),((694659986452826413540112797:ℚ)/2334720000000000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-11:ℚ)/16),((-5:ℚ)/8),((880052637:ℚ)/1250000000),((7132765093:ℚ)/10000000000),((-69500416023:ℚ)/107275000000),((-760052637:ℚ)/1346875000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((154454403:ℚ)/400000000),((3957516785630410151257094167137753443741188962064061700849:ℚ)/69984227796645789146423339843750000000000000000000000000000),((10851770305406946567629653:ℚ)/36480000000000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((353508581:ℚ)/500000000),((7162514651:ℚ)/10000000000),((-69827661161:ℚ)/107750000000),((-305508581:ℚ)/541125000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((9390133:ℚ)/25000000),((6475353794332521975798958548703998987399775201675461172909303:ℚ)/114471416207949142456054687500000000000000000000000000000000000),((578638589259217379038519:ℚ)/1945600000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((709992159:ℚ)/1000000000),((449516479:ℚ)/625000000),((-1461560423:ℚ)/2254687500),((-613992159:ℚ)/1087000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((113995553:ℚ)/312500000),((324144372413034606838899060298517340905394267278399:ℚ)/5728380914500448852777481079101562500000000000000000),((6942190091207707295657197:ℚ)/23347200000000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((1782417753:ℚ)/2500000000),((7222012141:ℚ)/10000000000),((-70482133551:ℚ)/108700000000),((-1542417753:ℚ)/2729375000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((1768253963:ℚ)/5000000000),((6769680521203533923458360956918528747360135018781510280535633:ℚ)/119598315771687338867187500000000000000000000000000000000000000),((43379462847662283832685533:ℚ)/145920000000000000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7159419893:ℚ)/10000000000),((906470011:ℚ)/1250000000),((-8851170121:ℚ)/13646875000),((-6199419893:ℚ)/10965000000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((3421695417:ℚ)/10000000000),((13517083387119013533918598206010532022585212816146580104693:ℚ)/238729969844331673979759216308593750000000000000000000000000),((231307832139578168938149271:ℚ)/778240000000000000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-11:ℚ)/16),((-5:ℚ)/8),((7189168241:ℚ)/10000000000),((910188439:ℚ)/1250000000),((-8892072829:ℚ)/13706250000),((-6229168241:ℚ)/11012500000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((3303058537:ℚ)/10000000000),((130045210319799443747292175237908627330840484704008012411:ℚ)/2296089864675908088684082031250000000000000000000000000000),((12171496169580753041672821:ℚ)/40960000000000000000000000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((7218916063:ℚ)/10000000000),((7311254419:ℚ)/10000000000),((-71463798609:ℚ)/110125000000),((-6258916063:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3180168727:ℚ)/10000000000),((28245518074818672189595801217358170025042638516856253958243:ℚ)/498560748001024723052978515625000000000000000000000000000000),((231208920428762009566646351:ℚ)/778240000000000000000000000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((1812165841:ℚ)/2500000000),((7341000817:ℚ)/10000000000),((-71791008987:ℚ)/110600000000),((-1572165841:ℚ)/2776875000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((763127947:ℚ)/2500000000),((29559841563524034648683315610542900747851672231611470374840429:ℚ)/521612567337792656250000000000000000000000000000000000000000000),((14447456984804041964476399:ℚ)/48640000000000000000000000)⟩
theorem valid12 : Valid source16 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7278410153:ℚ)/10000000000),((921343339:ℚ)/1250000000),((-9014776729:ℚ)/13884375000),((-65138249:ℚ)/115000000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((2919461809:ℚ)/10000000000),((783805018874095286984161571760580264478617990942081991:ℚ)/13827215139985978603363037109375000000000000000000000000),((231109601196685115016346111:ℚ)/778240000000000000000000000)⟩
theorem valid13 : Valid source16 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source16 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-11:ℚ)/16),((-5:ℚ)/8),((1461631287:ℚ)/2000000000),((3715118509:ℚ)/5000000000),((-36386303599:ℚ)/55775000000),((-141070143:ℚ)/250000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1390121997:ℚ)/5000000000),((9108077770334377337493786508259891213430547236347839:ℚ)/158851037850379943847656250000000000000000000000000000),((27727174649417633735745853:ℚ)/93388800000000000000000000)⟩
theorem valid14 : Valid source16 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source16 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source16 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((7367647507:ℚ)/10000000000),((1887302967:ℚ)/2500000000),((-18520332637:ℚ)/28125000000),((-6407647507:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((309887887:ℚ)/1250000000),((2083096712068059915253912126843229686932759907436925231619:ℚ)/35541822910308837890625000000000000000000000000000000000000),((230959858140194477480373671:ℚ)/778240000000000000000000000)⟩
theorem valid15 : Valid source16 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((7486623849:ℚ)/10000000000),((486696239:ℚ)/625000000),((-4793658629:ℚ)/7150000000),((-2175541283:ℚ)/3940000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((864729831:ℚ)/5000000000),((1300939310310533615767008819875038974281928225969812199:ℚ)/21312640749511718750000000000000000000000000000000000000),((692276321956077786245933437:ℚ)/2334720000000000000000000000)⟩
theorem valid16 : Valid source16 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-11:ℚ)/16),((-5:ℚ)/8),((1544910929:ℚ)/2000000000),((8025041053:ℚ)/10000000000),((-26438483861:ℚ)/39400000000),((-1352910929:ℚ)/2440000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((3251186203620176322047040270866572991276020961970640893521:ℚ)/53340811749375000000000000000000000000000000000000000000000),((303375823:ℚ)/1024000000)⟩
theorem valid17 : Valid source16 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source16 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((995307317:ℚ)/1250000000),((8500772763:ℚ)/10000000000),((-84548500393:ℚ)/122000000000),((-875307317:ℚ)/1620000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((60718358909511389928250594459362095161676457306067579112599:ℚ)/930763963125000000000000000000000000000000000000000000000000),((303375823:ℚ)/1024000000)⟩
theorem valid18 : Valid source16 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((8438195099:ℚ)/10000000000),((5201501653:ℚ)/5000000000),((-52736518183:ℚ)/64800000000),((-7478195099:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((5649373644236392011743913294305631146294094595969765267:ℚ)/63772920000000000000000000000000000000000000000000000000),((303375823:ℚ)/1024000000)⟩
theorem valid19 : Valid source16 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((2585110107:ℚ)/2500000000),((14205619891:ℚ)/10000000000),((-147301818801:ℚ)/160000000000),((-33987103:ℚ)/80000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1451166872868471502602918895788584621:ℚ)/12800000000000000000000000000000000000),((303375823:ℚ)/1024000000)⟩
theorem valid20 : Valid source16 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source16 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4291:ℚ)/6400) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source16 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4291:ℚ)/6400) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((4291:ℚ)/6400) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source16 nn0 nn1 Qcell ((4291:ℚ)/6400) ((4329:ℚ)/6400) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source16 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source16 nn0 nn1 Qcell ((4329:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source16 nn0 nn1 Qcell ((4291:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source16 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source16 nn0 nn1 Qcell ((4443:ℚ)/6400) ((45:ℚ)/64) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source16 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((61:ℚ)/80) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound source16 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC06
#check @N11Formalization.C450Source16GroupedC06.bound
#print axioms N11Formalization.C450Source16GroupedC06.valid0
#print axioms N11Formalization.C450Source16GroupedC06.valid1
#print axioms N11Formalization.C450Source16GroupedC06.valid2
#print axioms N11Formalization.C450Source16GroupedC06.valid3
#print axioms N11Formalization.C450Source16GroupedC06.valid4
#print axioms N11Formalization.C450Source16GroupedC06.valid5
#print axioms N11Formalization.C450Source16GroupedC06.valid6
#print axioms N11Formalization.C450Source16GroupedC06.valid7
#print axioms N11Formalization.C450Source16GroupedC06.valid8
#print axioms N11Formalization.C450Source16GroupedC06.valid9
#print axioms N11Formalization.C450Source16GroupedC06.valid10
#print axioms N11Formalization.C450Source16GroupedC06.valid11
#print axioms N11Formalization.C450Source16GroupedC06.valid12
#print axioms N11Formalization.C450Source16GroupedC06.valid13
#print axioms N11Formalization.C450Source16GroupedC06.valid14
#print axioms N11Formalization.C450Source16GroupedC06.valid15
#print axioms N11Formalization.C450Source16GroupedC06.valid16
#print axioms N11Formalization.C450Source16GroupedC06.valid17
#print axioms N11Formalization.C450Source16GroupedC06.valid18
#print axioms N11Formalization.C450Source16GroupedC06.valid19
#print axioms N11Formalization.C450Source16GroupedC06.valid20
#print axioms N11Formalization.C450Source16GroupedC06.bound
#print axioms N11Formalization.C450Source16GroupedC06.endpoint_checks
