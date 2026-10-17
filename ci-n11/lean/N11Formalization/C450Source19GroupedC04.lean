import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((167341599:ℚ)/250000000),((6889793937:ℚ)/10000000000),((-78687321181:ℚ)/99200000000),((-143341599:ℚ)/210625000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4933627877:ℚ)/10000000000),((164251637705645291626710786802794808690378064564174315698304869:ℚ)/2078720458137600000000000000000000000000000000000000000000000000),((7023486494066334056958011:ℚ)/13862400000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((1703180439:ℚ)/2500000000),((3504400967:ℚ)/5000000000),((-40117212571:ℚ)/50550000000),((-4389541317:ℚ)/6437500000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((114798089:ℚ)/250000000),((2030273706449449961549165724633300200612186582933208515640091:ℚ)/25694442627138281250000000000000000000000000000000000000000000),((703663373732773549753317131:ℚ)/1386240000000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((3465884077:ℚ)/5000000000),((441768899:ℚ)/625000000),((-5062995687:ℚ)/6437500000),((-271444007:ℚ)/393750000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((4224803183:ℚ)/10000000000),((41945676173959141036344597398556637764034204529781313807:ℚ)/551482323074340820312500000000000000000000000000000000000),((938959242755650892705394673:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((3495643637:ℚ)/5000000000),((28392207:ℚ)/40000000),((-325578691:ℚ)/415800000),((-9046930911:ℚ)/13053125000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((805910117:ℚ)/2000000000),((13295846432140384976672301450507554729455226327249714467:ℚ)/178159812258382762500000000000000000000000000000000000000),((939328218654809328405258753:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((877630731:ℚ)/1250000000),((3563900277:ℚ)/5000000000),((-40890703601:ℚ)/52212500000),((-2272892193:ℚ)/3278125000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3928498591:ℚ)/10000000000),((18270402838744723708742129955566060485466055954208478040094267:ℚ)/244734089450337014770507812500000000000000000000000000000000000),((176205745553376700274543171:ℚ)/346560000000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-13:ℚ)/16),((-3:ℚ)/4),((110168809:ℚ)/156250000),((1789387201:ℚ)/2500000000),((-20542033613:ℚ)/26225000000),((-380675236:ℚ)/548828125),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((478115269:ℚ)/1250000000),((6647161054604342187629384154412523729153590100669197424391:ℚ)/89010071060243164062500000000000000000000000000000000000000),((918163514336404462786247:ℚ)/1805000000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((3540280533:ℚ)/5000000000),((1796824127:ℚ)/2500000000),((-6879571217:ℚ)/8781250000),((-9180841599:ℚ)/13231250000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((185930491:ℚ)/500000000),((1416861076157504331735483252987146482339284461867831516202171:ℚ)/18966655594110298156738281250000000000000000000000000000000000),((2821903817933774699397939779:ℚ)/5544960000000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((222197429:ℚ)/312500000),((7217043671:ℚ)/10000000000),((-82941567723:ℚ)/105850000000),((-1153184574:ℚ)/1661328125),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((3609319311:ℚ)/10000000000),((10018794536005512699806978069984754364886134946740867455630712089:ℚ)/134073630591847278906250000000000000000000000000000000000000000000),((3676052649441543017778467:ℚ)/7220000000000000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4253:ℚ)/6400),((341:ℚ)/512),((-13:ℚ)/16),((-3:ℚ)/4),((714007377:ℚ)/1000000000),((7231917053:ℚ)/10000000000),((-83134921689:ℚ)/106325000000),((-1854022131:ℚ)/2664062500),((195067017:ℚ)/200000000),((2440069189:ℚ)/2500000000),((1112811311:ℚ)/5000000000),((69935417:ℚ)/200000000),((25870518660578859484303975789982994272114301369555590028123:ℚ)/349425778010618632812500000000000000000000000000000000000000),((112950284634863206951484219:ℚ)/221798400000000000000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((4253:ℚ)/6400) ((341:ℚ)/512) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((341:ℚ)/512),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((178873789:ℚ)/250000000),((3623395151:ℚ)/5000000000),((-41664136963:ℚ)/53281250000),((-154873789:ℚ)/222500000),((4873244381:ℚ)/5000000000),((1950670171:ℚ)/2000000000),((2256500263:ℚ)/10000000000),((3439175131:ℚ)/10000000000),((138628167216727237296154089452554201299765400922467583403841:ℚ)/1872075045949220657348632812500000000000000000000000000000000),((2353673880853515570432977:ℚ)/4620800000000000000000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((341:ℚ)/512) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((267:ℚ)/400),((8563:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((17924573:ℚ)/25000000),((7261663421:ℚ)/10000000000),((-27840541491:ℚ)/35600000000),((-93147438:ℚ)/133796875),((9739690061:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((1143344217:ℚ)/5000000000),((845159627:ℚ)/2500000000),((1531394666010109274027514949702823881989808643672417708672895177:ℚ)/20676732028384400000000000000000000000000000000000000000000000000),((23542166476371923154473:ℚ)/46208000000000000000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((8563:ℚ)/12800) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((8563:ℚ)/12800),((4291:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((56130521:ℚ)/78125000),((909567051:ℚ)/1250000000),((-10464371663:ℚ)/13379687500),((-1167132504:ℚ)/1676171875),((1216619291:ℚ)/1250000000),((4869845033:ℚ)/5000000000),((1158107867:ℚ)/5000000000),((3321111171:ℚ)/10000000000),((319033433088945109190992905320159654251988951760337419185321:ℚ)/4306802758434253002330660820007324218750000000000000000000000),((114978478035961464323571:ℚ)/225625000000000000000000)⟩
theorem valid11 : Valid source19 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source19 nn0 nn1 Qcell ((8563:ℚ)/12800) ((4291:ℚ)/6400) :=
  cell_of_packet source19 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-13:ℚ)/16),((-3:ℚ)/4),((3599792013:ℚ)/5000000000),((1826570499:ℚ)/2500000000),((-21025416487:ℚ)/26818750000),((-9359376039:ℚ)/13468750000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((652107757:ℚ)/2000000000),((19628530654519255197292621402162088621125556159666154818407:ℚ)/262440854237421709299087524414062500000000000000000000000000),((2827116979100877133409904659:ℚ)/5544960000000000000000000000)⟩
theorem valid12 : Valid source19 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source19 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source19 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7229338257:ℚ)/10000000000),((7336027073:ℚ)/10000000000),((-84488351949:ℚ)/107750000000),((-160752263:ℚ)/231250000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((392001913:ℚ)/1250000000),((50048661201369380910797013119515705281340324477523295320847:ℚ)/668983365960693359375000000000000000000000000000000000000000),((11313672238605074495719985339:ℚ)/22179840000000000000000000000)⟩
theorem valid13 : Valid source19 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source19 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source19 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((72590919:ℚ)/100000000),((1473154329:ℚ)/2000000000),((-16975006277:ℚ)/21645000000),((-188972757:ℚ)/271750000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((751629459:ℚ)/2500000000),((50487434632353570859228749655407476650408855776773352685201:ℚ)/674666113208617968750000000000000000000000000000000000000000),((1131887302783889746155371:ℚ)/2217984000000000000000000)⟩
theorem valid14 : Valid source19 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source19 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7288844963:ℚ)/10000000000),((3697757859:ℚ)/5000000000),((-42630852167:ℚ)/54350000000),((-18986534889:ℚ)/27293750000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((2871372849:ℚ)/10000000000),((89522717569687506322424371521334363451387147354204199512871261:ℚ)/1195983157716873388671875000000000000000000000000000000000000000),((3774690095100224409964671953:ℚ)/7393280000000000000000000000)⟩
theorem valid15 : Valid source19 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source19 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((7318597453:ℚ)/10000000000),((7425259301:ℚ)/10000000000),((-85648370913:ℚ)/109175000000),((-6358597453:ℚ)/9137500000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((1364870503:ℚ)/5000000000),((81347263439525308856163833303726141594010880804664610391694211:ℚ)/1086486618313758374023437500000000000000000000000000000000000000),((3776421337606690230086826033:ℚ)/7393280000000000000000000000)⟩
theorem valid16 : Valid source19 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source19 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((7348349379:ℚ)/10000000000),((935593127:ℚ)/1250000000),((-10802710651:ℚ)/13706250000),((-19165048137:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((129027687:ℚ)/500000000),((35180564607021674725190041675670448206824282169314377065243:ℚ)/461378660055844259262084960937500000000000000000000000000000),((11340493832368706223140643251:ℚ)/22179840000000000000000000000)⟩
theorem valid17 : Valid source19 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source19 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-13:ℚ)/16),((-3:ℚ)/4),((1481570313:ℚ)/2000000000),((3801855411:ℚ)/5000000000),((-556761017:ℚ)/700000000),((-429856771:ℚ)/625000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1126719769:ℚ)/5000000000),((1983331471642711362619958162703357627918774265937:ℚ)/25122070312500000000000000000000000000000000000000),((454487540313144387290048459:ℚ)/887193600000000000000000000)⟩
theorem valid18 : Valid source19 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source19 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((7526849473:ℚ)/10000000000),((12066671:ℚ)/15625000),((-15540747:ℚ)/19531250),((-19700548419:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1388563967:ℚ)/10000000000),((19238901651088394440835849394457774432333520922367041:ℚ)/243771076202392578125000000000000000000000000000000000),((3786242892653572528613779273:ℚ)/7393280000000000000000000000)⟩
theorem valid19 : Valid source19 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((7645839121:ℚ)/10000000000),((2168529423:ℚ)/2500000000),((-25470882499:ℚ)/28600000000),((-6685839121:ℚ)/10800000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((337807326827713643819743248643237147118653998742102758953:ℚ)/2960759587500000000000000000000000000000000000000000000000),((262155459:ℚ)/512000000)⟩
theorem valid20 : Valid source19 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((4298751351:ℚ)/5000000000),((10576187369:ℚ)/10000000000),((-42203478599:ℚ)/43200000000),((-11456254053:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((13682245990951056599171428291395385020651312328614407951:ℚ)/94478400000000000000000000000000000000000000000000000000),((262155459:ℚ)/512000000)⟩
theorem valid21 : Valid source19 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((10499879877:ℚ)/10000000000),((14378615373:ℚ)/10000000000),(-1:ℚ),((-9539879877:ℚ)/18400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((5637975300801605614094537:ℚ)/33856000000000000000000000),((262155459:ℚ)/512000000)⟩
theorem valid22 : Valid source19 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet22 valid22
private theorem node0_2 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source19 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source19 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source19 nn0 nn1 Qcell ((843:ℚ)/1280) ((4253:ℚ)/6400) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source19 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4253:ℚ)/6400) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source19 nn0 nn1 Qcell ((341:ℚ)/512) ((8563:ℚ)/12800) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source19 nn0 nn1 Qcell ((4253:ℚ)/6400) ((8563:ℚ)/12800) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source19 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8563:ℚ)/12800) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((8563:ℚ)/12800) :=
  cell_join node0_5 node5_11
private theorem node12_14 :
    CellBound source19 nn0 nn1 Qcell ((4291:ℚ)/6400) ((4329:ℚ)/6400) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source19 nn0 nn1 Qcell ((8563:ℚ)/12800) ((4329:ℚ)/6400) :=
  cell_join leaf11 node12_14
private theorem node15_17 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source19 nn0 nn1 Qcell ((4329:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_join leaf14 node15_17
private theorem node11_17 :
    CellBound source19 nn0 nn1 Qcell ((8563:ℚ)/12800) ((2193:ℚ)/3200) :=
  cell_join node11_14 node14_17
private theorem node18_20 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound source19 nn0 nn1 Qcell ((2193:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf17 node18_20
private theorem node21_23 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf20 node21_23
private theorem node17_23 :
    CellBound source19 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node17_20 node20_23
private theorem node11_23 :
    CellBound source19 nn0 nn1 Qcell ((8563:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node11_17 node17_23
private theorem node0_23 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_23
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_23
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22]
theorem packet_count : packets.length = 23 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC04
#check @N11Formalization.C450Source19GroupedC04.bound
#print axioms N11Formalization.C450Source19GroupedC04.valid0
#print axioms N11Formalization.C450Source19GroupedC04.valid1
#print axioms N11Formalization.C450Source19GroupedC04.valid2
#print axioms N11Formalization.C450Source19GroupedC04.valid3
#print axioms N11Formalization.C450Source19GroupedC04.valid4
#print axioms N11Formalization.C450Source19GroupedC04.valid5
#print axioms N11Formalization.C450Source19GroupedC04.valid6
#print axioms N11Formalization.C450Source19GroupedC04.valid7
#print axioms N11Formalization.C450Source19GroupedC04.valid8
#print axioms N11Formalization.C450Source19GroupedC04.valid9
#print axioms N11Formalization.C450Source19GroupedC04.valid10
#print axioms N11Formalization.C450Source19GroupedC04.valid11
#print axioms N11Formalization.C450Source19GroupedC04.valid12
#print axioms N11Formalization.C450Source19GroupedC04.valid13
#print axioms N11Formalization.C450Source19GroupedC04.valid14
#print axioms N11Formalization.C450Source19GroupedC04.valid15
#print axioms N11Formalization.C450Source19GroupedC04.valid16
#print axioms N11Formalization.C450Source19GroupedC04.valid17
#print axioms N11Formalization.C450Source19GroupedC04.valid18
#print axioms N11Formalization.C450Source19GroupedC04.valid19
#print axioms N11Formalization.C450Source19GroupedC04.valid20
#print axioms N11Formalization.C450Source19GroupedC04.valid21
#print axioms N11Formalization.C450Source19GroupedC04.valid22
#print axioms N11Formalization.C450Source19GroupedC04.bound
#print axioms N11Formalization.C450Source19GroupedC04.endpoint_checks
