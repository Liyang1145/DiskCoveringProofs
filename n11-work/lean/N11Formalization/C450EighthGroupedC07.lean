import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((6331823781:ℚ)/10000000000),((6608788253:ℚ)/10000000000),((-6224788253:ℚ)/9920000000),((-52506414029:ℚ)/103000000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5860447731:ℚ)/10000000000),((3142362758786524906927169625266573483915767152777053758273:ℚ)/194182790553600000000000000000000000000000000000000000000000),((1848122034744856632105984793:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((3284720509:ℚ)/5000000000),((6846420391:ℚ)/10000000000),((-6462420391:ℚ)/10300000000),((-27322484581:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5268402219:ℚ)/10000000000),((1966789506682442810297271114103404010494015376521830369393:ℚ)/121717836098437500000000000000000000000000000000000000000000),((1847203285281230817181372737:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((6807049907:ℚ)/10000000000),((6965232993:ℚ)/10000000000),((-2193744331:ℚ)/3560000000),((-56783449163:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((57609161:ℚ)/125000000),((5186587225474890905907082667226257693772698517254799852213:ℚ)/333187806544400000000000000000000000000000000000000000000000),((1845212327527943742073785873:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((1385170299:ℚ)/2000000000),((87807981:ℚ)/125000000),((-83007981:ℚ)/135875000),((-11570532691:ℚ)/21930000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((530468769:ℚ)/1250000000),((32018702522259609878611422881375092712594965265068207:ℚ)/2094466658168283081054687500000000000000000000000000000),((288160026987982674912697:ℚ)/2310400000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((3492625809:ℚ)/5000000000),((3542021721:ℚ)/5000000000),((-1116673907:ℚ)/1827500000),((-29193632281:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1012438721:ℚ)/2500000000),((2090372518895581243170394443607772406654265720159804537:ℚ)/136704788164694595336914062500000000000000000000000000000),((461005314412834897045006657:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((7044651309:ℚ)/10000000000),((7113745731:ℚ)/10000000000),((-6729745731:ℚ)/11060000000),((-58921861781:ℚ)/111075000000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((240409611:ℚ)/625000000),((632476924118945507236501377200157184159197733213310947139293:ℚ)/41729005387023412500000000000000000000000000000000000000000000),((1843531445226840669508068697:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((1768587749:ℚ)/2500000000),((3571723947:ℚ)/5000000000),((-1126574649:ℚ)/1851250000),((-14797289741:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3741033741:ℚ)/10000000000),((186996499716173777139641611152456915857209797885852467647:ℚ)/12335432746868439483642578125000000000000000000000000000000),((460858257169799263934448393:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((355202529:ℚ)/500000000),((1793287483:ℚ)/2500000000),((-1697287483:ℚ)/2788750000),((-2972822761:ℚ)/5601250000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((3632598347:ℚ)/10000000000),((1650699618540611845838822890703044083413812980229765309461:ℚ)/108872613008126050292968750000000000000000000000000000000000),((115208489244104175731189353:ℚ)/924160000000000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-5:ℚ)/8),((-9:ℚ)/16),((356687503:ℚ)/500000000),((900356481:ℚ)/1250000000),((-852356481:ℚ)/1400312500),((-2986187527:ℚ)/5625000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((1760488881:ℚ)/5000000000),((5269841863565377735609232649524328816913951466734183:ℚ)/347520110508012771606445312500000000000000000000000000),((28800622545840858405551697:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((44771559:ℚ)/62500000),((3616276821:ℚ)/5000000000),((-1141425607:ℚ)/1875000000),((-374944031:ℚ)/706093750),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((851464577:ℚ)/2500000000),((4253349761593310920879506161764769648783668706138381618363:ℚ)/280444715881347656250000000000000000000000000000000000000000),((24251908864422528282070003:ℚ)/194560000000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7193148719:ℚ)/10000000000),((7262255317:ℚ)/10000000000),((-6878255317:ℚ)/11297500000),((-60258338471:ℚ)/113450000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((3286871853:ℚ)/10000000000),((1759479015002766068093260523767852236916153461727194027339:ℚ)/115994144936326073974609375000000000000000000000000000000000),((1843051520220737487887199753:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((72228479:ℚ)/100000000),((7291956873:ℚ)/10000000000),((-6907956873:ℚ)/11345000000),((-605256311:ℚ)/1139250000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((3163581541:ℚ)/10000000000),((2875158665526854925412510917920442098560513922515540425208679:ℚ)/189518484637218860156250000000000000000000000000000000000000000),((1842959182453667558456304033:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((7252546983:ℚ)/10000000000),((7321658313:ℚ)/10000000000),((-2312552771:ℚ)/3797500000),((-60792922847:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((3035462433:ℚ)/10000000000),((263518382680183001640583222989140991223802935084734561:ℚ)/17367623417675781250000000000000000000000000000000000000),((1842868060410558012306503713:ℚ)/14786560000000000000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7282245971:ℚ)/10000000000),((7381060847:ℚ)/10000000000),((-6997060847:ℚ)/11440000000),((-61060213739:ℚ)/115350000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1450937209:ℚ)/5000000000),((9925935282066867191002548729006468475437145708392513947:ℚ)/648473240897625000000000000000000000000000000000000000000),((1843079630195989349778580593:ℚ)/14786560000000000000000000000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((7341643661:ℚ)/10000000000),((7440462931:ℚ)/10000000000),((-7056462931:ℚ)/11535000000),((-61594792949:ℚ)/116300000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1307452141:ℚ)/5000000000),((66209181062071895475051767544052872856092708910991972351359:ℚ)/4324849396020850781250000000000000000000000000000000000000000),((1842905893354958158056781497:ℚ)/14786560000000000000000000000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((370052049:ℚ)/500000000),((14764191:ℚ)/19531250),((-56056764:ℚ)/90859375),((-3106468441:ℚ)/5910000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((91728023:ℚ)/400000000),((181259942394440526026079351207550196054330927614085357:ℚ)/11643986115135765075683593750000000000000000000000000000),((14063669816266077022499:ℚ)/112812500000000000000000)⟩
theorem valid15 : Valid eighth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/8),((-9:ℚ)/16),((3759917271:ℚ)/5000000000),((1949216643:ℚ)/2500000000),((-617738881:ℚ)/985000000),((-31599255439:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1453731931:ℚ)/10000000000),((1070754789909965877550970950559795087967552792527272541:ℚ)/66676014686718750000000000000000000000000000000000000000),((3787455043000351:ℚ)/30400000000000000)⟩
theorem valid16 : Valid eighth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((7757417593:ℚ)/10000000000),((8272050391:ℚ)/10000000000),((-7888050391:ℚ)/12200000000),((-65336758337:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1262963377375330912560310780230391600492111221308148922417:ℚ)/74461117050000000000000000000000000000000000000000000000000),((127504499:ℚ)/1024000000)⟩
theorem valid17 : Valid eighth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((8232569077:ℚ)/10000000000),((10172610967:ℚ)/10000000000),((-9788610967:ℚ)/12960000000),((-69613121693:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((888415272178974091261867753602466833591566959501711163:ℚ)/40814668800000000000000000000000000000000000000000000000),((127504499:ℚ)/1024000000)⟩
theorem valid18 : Valid eighth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((5066515527:ℚ)/5000000000),((3493317229:ℚ)/2500000000),((-3397317229:ℚ)/4000000000),((-43358639743:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((12626232349156425270661537984217396202957792442517795083:ℚ)/476100000000000000000000000000000000000000000000000000000),((127504499:ℚ)/1024000000)⟩
theorem valid19 : Valid eighth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet19 valid19
private theorem node0_2 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound eighth nn0 nn1 Qcell ((4481:ℚ)/6400) ((4519:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound eighth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4519:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((4519:ℚ)/6400) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((4519:ℚ)/6400) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound eighth nn0 nn1 Qcell ((4519:ℚ)/6400) ((4557:ℚ)/6400) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound eighth nn0 nn1 Qcell ((4557:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound eighth nn0 nn1 Qcell ((4519:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_join node10_12 node12_15
private theorem node15_17 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf15 leaf16
private theorem node18_20 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf17 node18_20
private theorem node15_20 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node15_17 node17_20
private theorem node10_20 :
    CellBound eighth nn0 nn1 Qcell ((4519:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node10_15 node15_20
private theorem node0_20 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_20
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_20
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19]
theorem packet_count : packets.length = 20 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC07
#check @N11Formalization.C450EighthGroupedC07.bound
#print axioms N11Formalization.C450EighthGroupedC07.valid0
#print axioms N11Formalization.C450EighthGroupedC07.valid1
#print axioms N11Formalization.C450EighthGroupedC07.valid2
#print axioms N11Formalization.C450EighthGroupedC07.valid3
#print axioms N11Formalization.C450EighthGroupedC07.valid4
#print axioms N11Formalization.C450EighthGroupedC07.valid5
#print axioms N11Formalization.C450EighthGroupedC07.valid6
#print axioms N11Formalization.C450EighthGroupedC07.valid7
#print axioms N11Formalization.C450EighthGroupedC07.valid8
#print axioms N11Formalization.C450EighthGroupedC07.valid9
#print axioms N11Formalization.C450EighthGroupedC07.valid10
#print axioms N11Formalization.C450EighthGroupedC07.valid11
#print axioms N11Formalization.C450EighthGroupedC07.valid12
#print axioms N11Formalization.C450EighthGroupedC07.valid13
#print axioms N11Formalization.C450EighthGroupedC07.valid14
#print axioms N11Formalization.C450EighthGroupedC07.valid15
#print axioms N11Formalization.C450EighthGroupedC07.valid16
#print axioms N11Formalization.C450EighthGroupedC07.valid17
#print axioms N11Formalization.C450EighthGroupedC07.valid18
#print axioms N11Formalization.C450EighthGroupedC07.valid19
#print axioms N11Formalization.C450EighthGroupedC07.bound
#print axioms N11Formalization.C450EighthGroupedC07.endpoint_checks
