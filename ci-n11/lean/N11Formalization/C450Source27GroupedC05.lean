import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((6844825411:ℚ)/10000000000),((7061194281:ℚ)/10000000000),((-17183582843:ℚ)/24800000000),((-19551026507:ℚ)/33700000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((561960003:ℚ)/1250000000),((2928274758132389511535291300387158511005423171455613746497349:ℚ)/10826669052800000000000000000000000000000000000000000000000000),((6583782807086709751826037:ℚ)/12160000000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((870547851:ℚ)/1250000000),((3560460477:ℚ)/5000000000),((-8681381431:ℚ)/12637500000),((-7496026361:ℚ)/12756250000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((257430711:ℚ)/625000000),((966143068677222098156194182252727703655321438459833435113:ℚ)/3649110717539817810058593750000000000000000000000000000000),((1951079721642299141311743:ℚ)/3610000000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((4101:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7024150119:ℚ)/10000000000),((286031273:ℚ)/400000000),((-698093819:ℚ)/1020500000),((-60625651309:ℚ)/102525000000),((4940065779:ℚ)/5000000000),((1979272569:ℚ)/2000000000),((774947369:ℚ)/5000000000),((3917815213:ℚ)/10000000000),((2438997276940380219626835294850299365174628322576450163831:ℚ)/9309306666309708398437500000000000000000000000000000000000),((124755697252915264018374023:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((4101:ℚ)/6400),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((3527015511:ℚ)/5000000000),((1795160271:ℚ)/2500000000),((-4385480813:ℚ)/6407812500),((-30477170621:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((9880131563:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((95338219:ℚ)/250000000),((12197040399722631268685674660451305099924378044262891821671:ℚ)/46521379558010673522949218750000000000000000000000000000000),((31180392395163150442419303:ℚ)/57760000000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((4101:ℚ)/6400) ((103:ℚ)/160) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((1770977531:ℚ)/2500000000),((7210498751:ℚ)/10000000000),((-17631496253:ℚ)/25750000000),((-15320752841:ℚ)/25868750000),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((3706463043:ℚ)/10000000000),((4796301756634157480246062490413156957560000730153597226895179:ℚ)/18281110353874023437500000000000000000000000000000000000000000),((7792943968555711641851423:ℚ)/14440000000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4139:ℚ)/6400),((2079:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((7113787449:ℚ)/10000000000),((7240354851:ℚ)/10000000000),((-17721064553:ℚ)/25868750000),((-61611661939:ℚ)/103950000000),((4916570841:ℚ)/5000000000),((1969704979:ℚ)/2000000000),((1829340989:ℚ)/10000000000),((1798184621:ℚ)/5000000000),((398625296790129349920278165622821192015862112859936348514787:ℚ)/1518324537722521591186523437500000000000000000000000000000000),((124652299036731825467855943:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7143663023:ℚ)/10000000000),((7270209403:ℚ)/10000000000),((-1619148019:ℚ)/2362500000),((-61940293253:ℚ)/104425000000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((108842487:ℚ)/312500000),((10493318501854067873911282113890655209639458597523040096493:ℚ)/39941274485440063476562500000000000000000000000000000000000),((124617156219446469163250647:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((717353687:ℚ)/1000000000),((730006243:ℚ)/1000000000),((-1790018729:ℚ)/2610625000),((-6226890557:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3365898271:ℚ)/10000000000),((2010576488182164072873430489622627757129886506811516498093:ℚ)/7647940295323031711578369140625000000000000000000000000000),((1245816750747784558558567:ℚ)/2310400000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-3:ℚ)/4),((-11:ℚ)/16),((3601704507:ℚ)/5000000000),((7329913953:ℚ)/10000000000),((-17989741859:ℚ)/26225000000),((-31298749577:ℚ)/52687500000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((1622394721:ℚ)/5000000000),((210735416097533169346432957099856643467229132922844277422677:ℚ)/801090639542188476562500000000000000000000000000000000000000),((31136463907070232815807007:ℚ)/57760000000000000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((3616639739:ℚ)/5000000000),((7359763991:ℚ)/10000000000),((-18079291973:ℚ)/26343750000),((-31463037129:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((389895123:ℚ)/1250000000),((4992534559068490139787347522567629275615948868781993965226433:ℚ)/18966655594110298156738281250000000000000000000000000000000000),((31127424476019562369190303:ℚ)/57760000000000000000000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((1815787071:ℚ)/2500000000),((1477922513:ℚ)/2000000000),((-3633767539:ℚ)/5292500000),((-15813657781:ℚ)/26581250000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((1494221127:ℚ)/5000000000),((4414209511299584569578564163117458694054606655951755973060037:ℚ)/16759203823980909863281250000000000000000000000000000000000000),((7779575120694174911711863:ℚ)/14440000000000000000000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((227906733:ℚ)/312500000),((3709729847:ℚ)/5000000000),((-9129189541:ℚ)/13290625000),((-1986974063:ℚ)/3337500000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((712983163:ℚ)/2500000000),((68919551612150257581961800221743869979387683671872322399723:ℚ)/261504256297352457046508789062500000000000000000000000000000),((121519890359997019973827:ℚ)/225625000000000000000000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-3:ℚ)/4),((-11:ℚ)/16),((1464576203:ℚ)/2000000000),((3739574849:ℚ)/5000000000),((-9218724547:ℚ)/13350000000),((-12782338233:ℚ)/21550000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2708756049:ℚ)/10000000000),((959027902460125510276504057320640139202287067386490913367:ℚ)/3596806999758911132812500000000000000000000000000000000000),((4977813284226078680381887:ℚ)/9241600000000000000000000)⟩
theorem valid12 : Valid source27 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source27 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((3691303691:ℚ)/5000000000),((942354269:ℚ)/1250000000),((-2327062807:ℚ)/3367187500),((-32284340601:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((299696249:ℚ)/1250000000),((150497106507788589776490126366588971219071880143030285476503:ℚ)/563859630899900197982788085937500000000000000000000000000000),((31092492131225779517086783:ℚ)/57760000000000000000000000)⟩
theorem valid13 : Valid source27 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source27 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((3721163777:ℚ)/5000000000),((7658186991:ℚ)/10000000000),((-18974560973:ℚ)/27175000000),((-32612801547:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1020257551:ℚ)/5000000000),((23361881538726325125413010742738491527837464648257145313517:ℚ)/85617180983827209472656250000000000000000000000000000000000),((31073887747205232743280247:ℚ)/57760000000000000000000000)⟩
theorem valid14 : Valid source27 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((7561749957:ℚ)/10000000000),((7896832163:ℚ)/10000000000),((-249246791:ℚ)/350000000),((-66539249527:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1003705911:ℚ)/10000000000),((119840114576986055994237040796180225520388854743666461:ℚ)/421514843750000000000000000000000000000000000000000000),((123953569028196748245605407:ℚ)/231040000000000000000000000)⟩
theorem valid15 : Valid source27 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((7800527219:ℚ)/10000000000),((8850737267:ℚ)/10000000000),((-22552211801:ℚ)/28600000000),((-69165799409:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((8542874729055467875829931123859815340022352832003882441673:ℚ)/24597079650000000000000000000000000000000000000000000000000),((8576377:ℚ)/16000000)⟩
theorem valid16 : Valid source27 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((27359007:ℚ)/31250000),((5378155973:ℚ)/5000000000),((-14134467919:ℚ)/16200000000),((-248949077:ℚ)/500000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((229073560715148456215611192362449801044530304012965131:ℚ)/553584375000000000000000000000000000000000000000000000),((8576377:ℚ)/16000000)⟩
theorem valid17 : Valid source27 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((10661097957:ℚ)/10000000000),((14562844411:ℚ)/10000000000),((-39688533233:ℚ)/40000000000),((-100632077527:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((40997630390309545468216528978540232173037:ℚ)/76176000000000000000000000000000000000000),((8576377:ℚ)/16000000)⟩
theorem valid18 : Valid source27 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source27 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source27 nn0 nn1 Qcell ((4177:ℚ)/6400) ((843:ℚ)/1280) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source27 nn0 nn1 Qcell ((2079:ℚ)/3200) ((843:ℚ)/1280) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((843:ℚ)/1280) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((843:ℚ)/1280) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source27 nn0 nn1 Qcell ((843:ℚ)/1280) ((4253:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source27 nn0 nn1 Qcell ((4253:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source27 nn0 nn1 Qcell ((843:ℚ)/1280) ((1087:ℚ)/1600) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source27 nn0 nn1 Qcell ((843:ℚ)/1280) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC05
#check @N11Formalization.C450Source27GroupedC05.bound
#print axioms N11Formalization.C450Source27GroupedC05.valid0
#print axioms N11Formalization.C450Source27GroupedC05.valid1
#print axioms N11Formalization.C450Source27GroupedC05.valid2
#print axioms N11Formalization.C450Source27GroupedC05.valid3
#print axioms N11Formalization.C450Source27GroupedC05.valid4
#print axioms N11Formalization.C450Source27GroupedC05.valid5
#print axioms N11Formalization.C450Source27GroupedC05.valid6
#print axioms N11Formalization.C450Source27GroupedC05.valid7
#print axioms N11Formalization.C450Source27GroupedC05.valid8
#print axioms N11Formalization.C450Source27GroupedC05.valid9
#print axioms N11Formalization.C450Source27GroupedC05.valid10
#print axioms N11Formalization.C450Source27GroupedC05.valid11
#print axioms N11Formalization.C450Source27GroupedC05.valid12
#print axioms N11Formalization.C450Source27GroupedC05.valid13
#print axioms N11Formalization.C450Source27GroupedC05.valid14
#print axioms N11Formalization.C450Source27GroupedC05.valid15
#print axioms N11Formalization.C450Source27GroupedC05.valid16
#print axioms N11Formalization.C450Source27GroupedC05.valid17
#print axioms N11Formalization.C450Source27GroupedC05.valid18
#print axioms N11Formalization.C450Source27GroupedC05.bound
#print axioms N11Formalization.C450Source27GroupedC05.endpoint_checks
