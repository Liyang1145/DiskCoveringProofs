import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((1598739389:ℚ)/2500000000),((1670432307:ℚ)/2500000000),((-1430432307:ℚ)/3100000000),((-9111175723:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5708503707:ℚ)/10000000000),((478879028707106416537199337407501009459624746015094315089:ℚ)/9924180761718750000000000000000000000000000000000000000000),((134393147644902253349578269:ℚ)/924160000000000000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((1658253449:ℚ)/2500000000),((6800765559:ℚ)/10000000000),((-5840765559:ℚ)/12875000000),((-9527774143:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((1274895191:ℚ)/2500000000),((135991679990741753362464266764387982324673417289842547511:ℚ)/2902710616381835937500000000000000000000000000000000000000),((132757597536292810524717189:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((52750209:ℚ)/78125000),((3459895833:ℚ)/5000000000),((-2979895833:ℚ)/6556250000),((-304251463:ℚ)/834375000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((2384473873:ℚ)/5000000000),((44566165036337718541231984442341039781310649515241817:ℚ)/952092980718612670898437500000000000000000000000000000),((128847036807325748342309:ℚ)/902500000000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-1:ℚ)/2),((-7:ℚ)/16),((6871030323:ℚ)/10000000000),((1395860211:ℚ)/2000000000),((-401286737:ℚ)/890000000),((-39777212261:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4415673941:ℚ)/10000000000),((376483035935473974844614536525868159665759362880013925753:ℚ)/8154609144973754882812500000000000000000000000000000000000),((2097933191381335973469387581:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((1386105749:ℚ)/2000000000),((879851011:ℚ)/1250000000),((-759851011:ℚ)/1683593750),((-8038740243:ℚ)/21740000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4228778757:ℚ)/10000000000),((1277536932061350773764003566389850378725527871031127033563:ℚ)/27678076589650000000000000000000000000000000000000000000000),((83655319540949431069227789:ℚ)/591462400000000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((3495012501:ℚ)/5000000000),((3549156413:ℚ)/5000000000),((-3069156413:ℚ)/6793750000),((-20305087507:ℚ)/54825000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4033783937:ℚ)/10000000000),((4305255729672900581229978641753169392738766717339003962473:ℚ)/93296260440747070312500000000000000000000000000000000000000),((521207882173306842310763789:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((440594947:ℚ)/625000000),((7157815327:ℚ)/10000000000),((-6197815327:ℚ)/13706250000),((-2564164629:ℚ)/6912500000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((382944839:ℚ)/1000000000),((1087818732949610669515307727440515872150683745937222969:ℚ)/23578862683677673339843750000000000000000000000000000000),((8118276584625630049478301:ℚ)/57760000000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-1:ℚ)/2),((-7:ℚ)/16),((7109011249:ℚ)/10000000000),((7187565757:ℚ)/10000000000),((-889652251:ℚ)/1975000000),((-13814359581:ℚ)/37025000000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3614183993:ℚ)/10000000000),((287175041260767076444336836821345756538155829376439390061:ℚ)/6265162198217773437500000000000000000000000000000000000000),((2071724813645765115457848789:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((111543071:ℚ)/156250000),((144346313:ℚ)/200000000),((-125146313:ℚ)/277687500),((-650801497:ℚ)/1742968750),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1750913183:ℚ)/5000000000),((70199907235025448489115023973675365269090622481923969:ℚ)/1531630124065186828374862670898437500000000000000000000),((504992026369521853919349:ℚ)/3610000000000000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-1:ℚ)/2),((-7:ℚ)/16),((3584250673:ℚ)/5000000000),((1811766253:ℚ)/2500000000),((-1571766253:ℚ)/3485937500),((-20929754711:ℚ)/56012500000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((3385902523:ℚ)/10000000000),((4492060119380821453399254336349144938475924203861825233711:ℚ)/98015430042026855468750000000000000000000000000000000000000),((516292386738009044430912981:ℚ)/3696640000000000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-1:ℚ)/2),((-7:ℚ)/16),((359912283:ℚ)/500000000),((7276813849:ℚ)/10000000000),((-6316813849:ℚ)/14003125000),((-2103385981:ℚ)/5625000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((3266032193:ℚ)/10000000000),((2676847407102613237723582805680095321905531868045930617:ℚ)/58412235975265502929687500000000000000000000000000000000),((5154728584851731097810221:ℚ)/36966400000000000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((7227989493:ℚ)/10000000000),((366815499:ℚ)/500000000),((-106271833:ℚ)/234375000),((-42275926451:ℚ)/113450000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1570881551:ℚ)/5000000000),((1051899678371895902874305741549486393897303694567807501:ℚ)/22815685759765625000000000000000000000000000000000000000),((2058613000222324865640883661:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((364373787:ℚ)/500000000),((1848951023:ℚ)/2500000000),((-1608951023:ℚ)/3545312500),((-2134616509:ℚ)/5720000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2877727449:ℚ)/10000000000),((122334508845290299128168451712231448340998864515520616039:ℚ)/2654010273200000000000000000000000000000000000000000000000),((5130137920227377106932141:ℚ)/36966400000000000000000000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((1469392027:ℚ)/2000000000),((7514786461:ℚ)/10000000000),((-6554786461:ℚ)/14300000000),((-8621744189:ℚ)/23260000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2587706849:ℚ)/10000000000),((524419870226014417294735865909614728114687035493937471677:ℚ)/11247219891050000000000000000000000000000000000000000000000),((81819841816310445401579181:ℚ)/591462400000000000000000000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((7465923547:ℚ)/10000000000),((7633761339:ℚ)/10000000000),((-6673761339:ℚ)/14537500000),((-14647154943:ℚ)/39400000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((940578419:ℚ)/5000000000),((5178711292970122001639384736702107824156948452471419462619:ℚ)/111144609987500000000000000000000000000000000000000000000000),((2032373909305785896932985901:ℚ)/14786560000000000000000000000)⟩
theorem valid14 : Valid source14 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/2),((-7:ℚ)/16),((7584880081:ℚ)/10000000000),((314867601:ℚ)/400000000),((-92155867:ℚ)/197000000),((-44774160567:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((630891917:ℚ)/10000000000),((106374212456187795973896569907477858430553096259734111574189:ℚ)/2235762850000000000000000000000000000000000000000000000000000),((2019246554152853276086084629:ℚ)/14786560000000000000000000000)⟩
theorem valid15 : Valid source14 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((3911386901:ℚ)/5000000000),((1669494359:ℚ)/2000000000),((-24221219:ℚ)/50000000),((-7739902769:ℚ)/21600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1036146385608329384787635793495530511325777994656960277:ℚ)/20995200000000000000000000000000000000000000000000000000),((139721439:ℚ)/1024000000)⟩
theorem valid16 : Valid source14 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((4149245911:ℚ)/5000000000),((1281231857:ℚ)/1250000000),((-1161231857:ℚ)/2025000000),((-24884721377:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((5033798663766274731171104659448927518479736266955364385389:ℚ)/86400000000000000000000000000000000000000000000000000000000),((139721439:ℚ)/1024000000)⟩
theorem valid17 : Valid source14 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((2040136131:ℚ)/2000000000),((14052650219:ℚ)/10000000000),((-13092650219:ℚ)/20000000000),((-12616952917:ℚ)/44160000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((27158485434997764710888832040496411444262366158677688761:ℚ)/403671859200000000000000000000000000000000000000000000000),((139721439:ℚ)/1024000000)⟩
theorem valid18 : Valid source14 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source14 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source14 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source14 nn0 nn1 Qcell ((1049:ℚ)/1600) ((431:ℚ)/640) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source14 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source14 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source14 nn0 nn1 Qcell ((431:ℚ)/640) ((2231:ℚ)/3200) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source14 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source14 nn0 nn1 Qcell ((2231:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source14 nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC09
#check @N11Formalization.C450Source14GroupedC09.bound
#print axioms N11Formalization.C450Source14GroupedC09.valid0
#print axioms N11Formalization.C450Source14GroupedC09.valid1
#print axioms N11Formalization.C450Source14GroupedC09.valid2
#print axioms N11Formalization.C450Source14GroupedC09.valid3
#print axioms N11Formalization.C450Source14GroupedC09.valid4
#print axioms N11Formalization.C450Source14GroupedC09.valid5
#print axioms N11Formalization.C450Source14GroupedC09.valid6
#print axioms N11Formalization.C450Source14GroupedC09.valid7
#print axioms N11Formalization.C450Source14GroupedC09.valid8
#print axioms N11Formalization.C450Source14GroupedC09.valid9
#print axioms N11Formalization.C450Source14GroupedC09.valid10
#print axioms N11Formalization.C450Source14GroupedC09.valid11
#print axioms N11Formalization.C450Source14GroupedC09.valid12
#print axioms N11Formalization.C450Source14GroupedC09.valid13
#print axioms N11Formalization.C450Source14GroupedC09.valid14
#print axioms N11Formalization.C450Source14GroupedC09.valid15
#print axioms N11Formalization.C450Source14GroupedC09.valid16
#print axioms N11Formalization.C450Source14GroupedC09.valid17
#print axioms N11Formalization.C450Source14GroupedC09.valid18
#print axioms N11Formalization.C450Source14GroupedC09.bound
#print axioms N11Formalization.C450Source14GroupedC09.endpoint_checks
