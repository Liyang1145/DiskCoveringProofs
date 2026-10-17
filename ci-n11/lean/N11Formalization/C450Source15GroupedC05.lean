import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((6545989817:ℚ)/10000000000),((6846834857:ℚ)/10000000000),((-18460504571:ℚ)/24800000000),((-63045887987:ℚ)/103000000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5329451691:ℚ)/10000000000),((57608060672497187842160855067661982186804951572143958041101:ℚ)/1011368700800000000000000000000000000000000000000000000000000),((75239936315586440748811037:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((6783915211:ℚ)/10000000000),((6965778341:ℚ)/10000000000),((-18817335023:ℚ)/25750000000),((-65663067321:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4676714857:ℚ)/10000000000),((1578989885953053175452660134100806479061941496949525418644537:ℚ)/29356393640795898437500000000000000000000000000000000000000000),((3961910689941547669608647:ℚ)/12160000000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((6902866321:ℚ)/10000000000),((7025247473:ℚ)/10000000000),((-18995742419:ℚ)/26225000000),((-66971529531:ℚ)/105850000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4316614529:ℚ)/10000000000),((361918101484329602308868466645128290232595436037590005835413:ℚ)/6920625742583691406250000000000000000000000000000000000000000),((75294194780242614752693453:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((3481169581:ℚ)/5000000000),((283388597:ℚ)/400000000),((-766965791:ℚ)/1058500000),((-33812865391:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((1031400753:ℚ)/2500000000),((10519607109838794558700877330663760155541662738685473:ℚ)/201071152050976562500000000000000000000000000000000000),((18829400738428209143242613:ℚ)/57760000000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((3510905129:ℚ)/5000000000),((1778612009:ℚ)/2500000000),((-4815836027:ℚ)/6675000000),((-34139956419:ℚ)/53637500000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((157034817:ℚ)/400000000),((3066138402792204164232889661689406409903549191688009928253:ℚ)/59419415185038757324218750000000000000000000000000000000000),((18831606763929492974896253:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-3:ℚ)/4),((-11:ℚ)/16),((3525772583:ℚ)/5000000000),((893022593:ℚ)/1250000000),((-2419067779:ℚ)/3352343750),((-34303498413:ℚ)/53875000000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((477788453:ℚ)/1250000000),((9030771709962359379095269074133684642019320882978523986799:ℚ)/174960569491614472866058349609375000000000000000000000000000),((18834522071688880144198237:ℚ)/57760000000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((885159957:ℚ)/1250000000),((3586956527:ℚ)/5000000000),((-9720869581:ℚ)/13468750000),((-8616759527:ℚ)/13528125000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((3716006739:ℚ)/10000000000),((923463573663247770242926554121009941483722728834717505408051:ℚ)/17886158782492053508758544921875000000000000000000000000000000),((1177339644074436553472917:ℚ)/3610000000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((7111013731:ℚ)/10000000000),((7203644971:ℚ)/10000000000),((-19530934913:ℚ)/27056250000),((-69261151041:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1803362589:ℚ)/5000000000),((7561255053504448567657080144810736466262435852669667257833:ℚ)/146411916928953552246093750000000000000000000000000000000000),((75361373860406595799341013:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7140747399:ℚ)/10000000000),((7233376501:ℚ)/10000000000),((-19620129503:ℚ)/27175000000),((-69588221389:ℚ)/109175000000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((3494182751:ℚ)/10000000000),((7722610549208489562835835344132284716889606040556934816621577:ℚ)/149497894714609173583984375000000000000000000000000000000000000),((75372998208340445403864733:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((896310083:ℚ)/1250000000),((7263107649:ℚ)/10000000000),((-19709322947:ℚ)/27293750000),((-2913136971:ℚ)/4568750000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((3378053023:ℚ)/10000000000),((877166300618508636401894082798874187444814697920639822921717:ℚ)/16976353411152474594116210937500000000000000000000000000000000),((1177884535423663061748237:ℚ)/3610000000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-3:ℚ)/4),((-11:ℚ)/16),((1800053383:ℚ)/2500000000),((364641921:ℚ)/500000000),((-989925763:ℚ)/1370625000),((-17560587213:ℚ)/27531250000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((65159037:ℚ)/200000000),((17931978745230607166331744660719306015531817153043029733:ℚ)/346964690662137222290039062500000000000000000000000000000),((4712263127442074953220637:ℚ)/14440000000000000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((7229946007:ℚ)/10000000000),((3661284409:ℚ)/5000000000),((-9943853227:ℚ)/13765625000),((-70569406077:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3133422027:ℚ)/10000000000),((1030916277031730088710347514854374582029452804564669535316127:ℚ)/19942429920040988922119140625000000000000000000000000000000000),((75407797526261301279115517:ℚ)/231040000000000000000000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((453729881:ℚ)/625000000),((229759339:ℚ)/312500000),((-624278017:ℚ)/864062500),((-4431028691:ℚ)/6942187500),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3003912219:ℚ)/10000000000),((1028851908006601778743845864950377156690390491903954359123:ℚ)/19897940343391138315200805664062500000000000000000000000000),((294606924730103538336413:ℚ)/902500000000000000000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((3644704901:ℚ)/5000000000),((1476405703:ℚ)/2000000000),((-4013217109:ℚ)/5553750000),((-35611753911:ℚ)/55775000000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((717186857:ℚ)/2500000000),((1913889639289516332916315085097292827803134193414547281611:ℚ)/37006298240605318450927734375000000000000000000000000000000),((18857733913906396976226533:ℚ)/57760000000000000000000000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/4),((-11:ℚ)/16),((7319141131:ℚ)/10000000000),((372074339:ℚ)/500000000),((-1012223017:ℚ)/1394375000),((-23850184147:ℚ)/37500000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((68177157:ℚ)/250000000),((7994502409490431809771509176804524520295303105543003:ℚ)/152496996336364746093750000000000000000000000000000000),((75457019332598409248441413:ℚ)/231040000000000000000000000)⟩
theorem valid14 : Valid source15 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source15 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source15 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((295144107:ℚ)/400000000),((7560399151:ℚ)/10000000000),((-20601197453:ℚ)/28125000000),((-2888185177:ℚ)/4576000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((604915017:ℚ)/2500000000),((16998148518346918482426787727615879659123357908803623051243:ℚ)/315927314758300781250000000000000000000000000000000000000000),((120814637353145287507717:ℚ)/369664000000000000000000)⟩
theorem valid15 : Valid source15 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((1874380361:ℚ)/2500000000),((7798208203:ℚ)/10000000000),((-21314624609:ℚ)/28600000000),((-18378183971:ℚ)/29550000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1644045811:ℚ)/10000000000),((240212195581844540970090868633026396565863442753523924706637:ℚ)/4255708104862500000000000000000000000000000000000000000000000),((4719772449467196998965693:ℚ)/14440000000000000000000000)⟩
theorem valid16 : Valid source15 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/4),((-11:ℚ)/16),((773534267:ℚ)/1000000000),((8035997967:ℚ)/10000000000),((-22027993901:ℚ)/29550000000),((-7612876937:ℚ)/12200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((11265166904536168629026808951937216318640244189833223810553:ℚ)/200028044060156250000000000000000000000000000000000000000000),((5228929:ℚ)/16000000)⟩
theorem valid17 : Valid source15 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((7973143847:ℚ)/10000000000),((1702305287:ℚ)/2000000000),((-4690915861:ℚ)/6100000000),((-78744582317:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((567779850830327973097556219909312885038947793917289472699:ℚ)/9307639631250000000000000000000000000000000000000000000000),((5228929:ℚ)/16000000)⟩
theorem valid18 : Valid source15 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((4224346563:ℚ)/5000000000),((650821103:ℚ)/625000000),((-1822463309:ℚ)/2025000000),((-41987812193:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((752569987930677222956736760040071694266378691432441:ℚ)/8649755859375000000000000000000000000000000000000000),((5228929:ℚ)/16000000)⟩
theorem valid19 : Valid source15 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((10350367767:ℚ)/10000000000),((3553757023:ℚ)/2500000000),(-1:ℚ),((-104894045437:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2742440632956034520070440321:ℚ)/24376320000000000000000000000),((5228929:ℚ)/16000000)⟩
theorem valid20 : Valid source15 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source15 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4291:ℚ)/6400) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source15 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4291:ℚ)/6400) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((4291:ℚ)/6400) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source15 nn0 nn1 Qcell ((4291:ℚ)/6400) ((4329:ℚ)/6400) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source15 nn0 nn1 Qcell ((4329:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source15 nn0 nn1 Qcell ((4291:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source15 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source15 nn0 nn1 Qcell ((4443:ℚ)/6400) ((45:ℚ)/64) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source15 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((61:ℚ)/80) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound source15 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC05
#check @N11Formalization.C450Source15GroupedC05.bound
#print axioms N11Formalization.C450Source15GroupedC05.valid0
#print axioms N11Formalization.C450Source15GroupedC05.valid1
#print axioms N11Formalization.C450Source15GroupedC05.valid2
#print axioms N11Formalization.C450Source15GroupedC05.valid3
#print axioms N11Formalization.C450Source15GroupedC05.valid4
#print axioms N11Formalization.C450Source15GroupedC05.valid5
#print axioms N11Formalization.C450Source15GroupedC05.valid6
#print axioms N11Formalization.C450Source15GroupedC05.valid7
#print axioms N11Formalization.C450Source15GroupedC05.valid8
#print axioms N11Formalization.C450Source15GroupedC05.valid9
#print axioms N11Formalization.C450Source15GroupedC05.valid10
#print axioms N11Formalization.C450Source15GroupedC05.valid11
#print axioms N11Formalization.C450Source15GroupedC05.valid12
#print axioms N11Formalization.C450Source15GroupedC05.valid13
#print axioms N11Formalization.C450Source15GroupedC05.valid14
#print axioms N11Formalization.C450Source15GroupedC05.valid15
#print axioms N11Formalization.C450Source15GroupedC05.valid16
#print axioms N11Formalization.C450Source15GroupedC05.valid17
#print axioms N11Formalization.C450Source15GroupedC05.valid18
#print axioms N11Formalization.C450Source15GroupedC05.valid19
#print axioms N11Formalization.C450Source15GroupedC05.valid20
#print axioms N11Formalization.C450Source15GroupedC05.bound
#print axioms N11Formalization.C450Source15GroupedC05.endpoint_checks
