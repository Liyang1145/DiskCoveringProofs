import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((6551865629:ℚ)/10000000000),((6852858663:ℚ)/10000000000),((-81407162619:ℚ)/99200000000),((-17575596887:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1062843003:ℚ)/2000000000),((3469935859537908459398824758098555676367356285489295146577989:ℚ)/64727596851200000000000000000000000000000000000000000000000000),((5085761501206370104595274951:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((1357933221:ℚ)/2000000000),((139434763:ℚ)/200000000),((-1659051919:ℚ)/2060000000),((-3657799663:ℚ)/5245000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4659901561:ℚ)/10000000000),((753843265246417778839988577662501163215893716134919925169:ℚ)/15030473544087500000000000000000000000000000000000000000000),((203748940518077628111316151:ℚ)/591462400000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((1727139541:ℚ)/2500000000),((1757794037:ℚ)/2500000000),((-20931322481:ℚ)/26225000000),((-4661418623:ℚ)/6615625000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((2149339493:ℚ)/5000000000),((335876652441502035851355636928694334361931192731215782509047:ℚ)/6920625742583691406250000000000000000000000000000000000000000),((318606358149486039060626391:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((3484001139:ℚ)/5000000000),((7090613023:ℚ)/10000000000),((-84497969299:ℚ)/105850000000),((-9412003417:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((4106979129:ℚ)/10000000000),((9759676803806368000306887843355265394639675579946269120997:ℚ)/201071152050976562500000000000000000000000000000000000000000),((67128033911380312306595549:ℚ)/194560000000000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((175686129:ℚ)/250000000),((7120331049:ℚ)/10000000000),((-28294767879:ℚ)/35600000000),((-475058387:ℚ)/670468750),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((3906444989:ℚ)/10000000000),((3874687699420375583846852808307373521953864845123127741381321:ℚ)/81127308199306250000000000000000000000000000000000000000000000),((3189824067034735266203951:ℚ)/9241600000000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-13:ℚ)/16),((-3:ℚ)/4),((141143323:ℚ)/200000000),((1430009761:ℚ)/2000000000),((-17054126893:ℚ)/21455000000),((-381829969:ℚ)/538750000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((950607373:ℚ)/2500000000),((6418510385644815349014218046251667255896948758958853506809:ℚ)/134369717369559915161132812500000000000000000000000000000000),((2042292997890234756145719:ℚ)/5914624000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((1771721711:ℚ)/2500000000),((1435953259:ℚ)/2000000000),((-17131392367:ℚ)/21550000000),((-4795165133:ℚ)/6764062500),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((14782539:ℚ)/40000000),((1166674511469843435336457380761426102864785674033887936916811:ℚ)/24420568791029150390625000000000000000000000000000000000000000),((319234147046200721285867631:ℚ)/924160000000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4329:ℚ)/6400),((8677:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((3558303623:ℚ)/5000000000),((3597312471:ℚ)/5000000000),((-4769451347:ℚ)/6012500000),((-9634910869:ℚ)/13557812500),((9700205687:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((306851119:ℚ)/1250000000),((448226493:ℚ)/1250000000),((4847483271948266953398332802962597588565521475549199357756477:ℚ)/102278530682823352050781250000000000000000000000000000000000000),((1277184975857218141365447519:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((4329:ℚ)/6400) ((8677:ℚ)/12800) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((8677:ℚ)/12800),((1087:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((3565733669:ℚ)/5000000000),((7209483523:ℚ)/10000000000),((-86043285799:ℚ)/108462500000),((-9657201007:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((2425051423:ℚ)/2500000000),((2480870833:ℚ)/10000000000),((3529676839:ℚ)/10000000000),((446631204979957849040139968126968931030100444612700271230941609:ℚ)/9422755817392408166503906250000000000000000000000000000000000000),((1277436680970503568723718071:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((8677:ℚ)/12800) ((1087:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1087:ℚ)/1600),((1743:ℚ)/2560),((-13:ℚ)/16),((-3:ℚ)/4),((7146327359:ℚ)/10000000000),((180608551:ℚ)/250000000),((-2155911163:ℚ)/2717500000),((-19358982077:ℚ)/27234375000),((9687532673:ℚ)/10000000000),((2423459781:ℚ)/2500000000),((2506424897:ℚ)/10000000000),((694534657:ℚ)/2000000000),((860149586037688447299686247834772536172294196137857414953:ℚ)/18145300093115917968750000000000000000000000000000000000000),((5110753512142068668082072591:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1743:ℚ)/2560) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1743:ℚ)/2560),((4367:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7161187309:ℚ)/10000000000),((1809800123:ℚ)/2500000000),((-3086771657:ℚ)/3890625000),((-19403561927:ℚ)/27293750000),((2420321489:ℚ)/2500000000),((4843766339:ℚ)/5000000000),((2531487941:ℚ)/10000000000),((3414757727:ℚ)/10000000000),((6932840953619670327879087400493511704517207379628259972061:ℚ)/146239025087933242321014404296875000000000000000000000000000),((5111760268140775931269825191:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((1743:ℚ)/2560) ((4367:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4367:ℚ)/6400),((8753:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((7176047189:ℚ)/10000000000),((7254058881:ℚ)/10000000000),((-86622765453:ℚ)/109175000000),((-19448141567:ℚ)/27353125000),((483754929:ℚ)/500000000),((9681285961:ℚ)/10000000000),((639018949:ℚ)/2500000000),((3355882879:ℚ)/10000000000),((73856545204159174631429106215871399313327073315616585006162987:ℚ)/1557770534161141300537109375000000000000000000000000000000000000),((5112766992014948360714223831:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((4367:ℚ)/6400) ((8753:ℚ)/12800) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((8753:ℚ)/12800),((2193:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((3595453499:ℚ)/5000000000),((1453783441:ℚ)/2000000000),((-17363184733:ℚ)/21882500000),((-9746360497:ℚ)/13706250000),((4834485079:ℚ)/5000000000),((1935019717:ℚ)/2000000000),((2580203419:ℚ)/10000000000),((411999659:ℚ)/1250000000),((73204943309426090541799148938551467389436976813384607481417:ℚ)/1543895582910090893554687500000000000000000000000000000000000),((1278443420907142164441409911:ℚ)/3696640000000000000000000000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((8753:ℚ)/12800) ((2193:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-13:ℚ)/16),((-3:ℚ)/4),((3602883369:ℚ)/5000000000),((3649316833:ℚ)/5000000000),((-43601118829:ℚ)/54825000000),((-9768650107:ℚ)/13765625000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((1617522351:ℚ)/5000000000),((9552686887918898638835799219045633966152610394072944800153659:ℚ)/199851661821391040039062500000000000000000000000000000000000000),((1278950123775084358925532671:ℚ)/3696640000000000000000000000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((723548601:ℚ)/1000000000),((3664174939:ℚ)/5000000000),((-43794274207:ℚ)/55062500000),((-1962645803:ℚ)/2765000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1554843173:ℚ)/5000000000),((102143342353173895664605252860734561820030883708578033662893:ℚ)/2136688920004391670227050781250000000000000000000000000000000),((51178137093990174302246111:ℚ)/147865600000000000000000000)⟩
theorem valid14 : Valid source14 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source14 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7265205009:ℚ)/10000000000),((1839516461:ℚ)/2500000000),((-21993713993:ℚ)/27650000000),((-19715615027:ℚ)/27768750000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((2979236681:ℚ)/10000000000),((10390935042047177330050601268872608821830791402626578366771069:ℚ)/217338569724080273437500000000000000000000000000000000000000000),((269464568190155586896919989:ℚ)/778240000000000000000000000)⟩
theorem valid15 : Valid source14 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((3647461869:ℚ)/5000000000),((3693890783:ℚ)/5000000000),((-44180580179:ℚ)/55537500000),((-9902385607:ℚ)/13943750000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((142149717:ℚ)/500000000),((15925135513098639970411661375743216266799334448325998365481029:ℚ)/333056684165447866058349609375000000000000000000000000000000000),((1280459938469945439292245671:ℚ)/3696640000000000000000000000)⟩
theorem valid16 : Valid source14 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source14 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-13:ℚ)/16),((-3:ℚ)/4),((36623211:ℚ)/50000000),((930901537:ℚ)/1250000000),((-11141719981:ℚ)/13943750000),((-99469633:ℚ)/140625000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((54001639:ℚ)/200000000),((28926091963207325990542187935874139639062243380559771:ℚ)/595691391938924789428710937500000000000000000000000000),((128147320233615274540631:ℚ)/369664000000000000000000)⟩
theorem valid17 : Valid source14 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source14 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source14 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((369203917:ℚ)/500000000),((118219859:ℚ)/156250000),((-1416858167:ℚ)/1757812500),((-1003611751:ℚ)/1430000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((119470293:ℚ)/500000000),((34718645062954049942945381654702843619121533180616737293:ℚ)/694176228716969490051269531250000000000000000000000000000),((12834995989539694369275879:ℚ)/36966400000000000000000000)⟩
theorem valid18 : Valid source14 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((468934223:ℚ)/625000000),((7803777839:ℚ)/10000000000),((-93769111907:ℚ)/114400000000),((-1276802669:ℚ)/1846875000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((799916523:ℚ)/5000000000),((4793947280076057908432421532107426195245193201327154896445933:ℚ)/90788439570400000000000000000000000000000000000000000000000000),((20063344891621521780451119:ℚ)/57760000000000000000000000)⟩
theorem valid19 : Valid source14 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-13:ℚ)/16),((-3:ℚ)/4),((7740674509:ℚ)/10000000000),((40207359:ℚ)/50000000),((-161431889:ℚ)/197000000),((-21142023527:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((28073485934684331914776666818802205235020276571934853:ℚ)/533408117493750000000000000000000000000000000000000000),((71137449:ℚ)/204800000)⟩
theorem valid20 : Valid source14 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((3989193647:ℚ)/5000000000),((8516825561:ℚ)/10000000000),((-103038732293:ℚ)/122000000000),((-10927580941:ℚ)/16200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1429854602242732222701967124543231375029443653253763582700881:ℚ)/24820372350000000000000000000000000000000000000000000000000000),((71137449:ℚ)/204800000)⟩
theorem valid21 : Valid source14 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((1056721923:ℚ)/1250000000),((10417904259:ℚ)/10000000000),((-42584251789:ℚ)/43200000000),((-2910165769:ℚ)/5000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((8103709751494462430692318988207604850994363389989973513:ℚ)/94478400000000000000000000000000000000000000000000000000),((71137449:ℚ)/204800000)⟩
theorem valid22 : Valid source14 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((10354958727:ℚ)/10000000000),((14219170117:ℚ)/10000000000),(-1:ℚ),((-28984876181:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((3044289565264906985335961:ℚ)/31740000000000000000000000),((71137449:ℚ)/204800000)⟩
theorem valid23 : Valid source14 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source14 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source14 nn0 nn1 packet23 valid23
private theorem node1_3 :
    CellBound source14 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source14 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source14 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source14 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source14 nn0 nn1 Qcell ((1743:ℚ)/2560) ((8753:ℚ)/12800) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source14 nn0 nn1 Qcell ((1087:ℚ)/1600) ((8753:ℚ)/12800) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source14 nn0 nn1 Qcell ((431:ℚ)/640) ((8753:ℚ)/12800) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((8753:ℚ)/12800) :=
  cell_join node0_6 node6_12
private theorem node13_15 :
    CellBound source14 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source14 nn0 nn1 Qcell ((8753:ℚ)/12800) ((553:ℚ)/800) :=
  cell_join leaf12 node13_15
private theorem node16_18 :
    CellBound source14 nn0 nn1 Qcell ((4443:ℚ)/6400) ((45:ℚ)/64) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf15 node16_18
private theorem node12_18 :
    CellBound source14 nn0 nn1 Qcell ((8753:ℚ)/12800) ((45:ℚ)/64) :=
  cell_join node12_15 node15_18
private theorem node19_21 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((61:ℚ)/80) :=
  cell_join leaf18 node19_21
private theorem node22_24 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf22 leaf23
private theorem node21_24 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf21 node22_24
private theorem node18_24 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node18_21 node21_24
private theorem node12_24 :
    CellBound source14 nn0 nn1 Qcell ((8753:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node12_18 node18_24
private theorem node0_24 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_12 node12_24
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_24
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23]
theorem packet_count : packets.length = 24 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC04
#check @N11Formalization.C450Source14GroupedC04.bound
#print axioms N11Formalization.C450Source14GroupedC04.valid0
#print axioms N11Formalization.C450Source14GroupedC04.valid1
#print axioms N11Formalization.C450Source14GroupedC04.valid2
#print axioms N11Formalization.C450Source14GroupedC04.valid3
#print axioms N11Formalization.C450Source14GroupedC04.valid4
#print axioms N11Formalization.C450Source14GroupedC04.valid5
#print axioms N11Formalization.C450Source14GroupedC04.valid6
#print axioms N11Formalization.C450Source14GroupedC04.valid7
#print axioms N11Formalization.C450Source14GroupedC04.valid8
#print axioms N11Formalization.C450Source14GroupedC04.valid9
#print axioms N11Formalization.C450Source14GroupedC04.valid10
#print axioms N11Formalization.C450Source14GroupedC04.valid11
#print axioms N11Formalization.C450Source14GroupedC04.valid12
#print axioms N11Formalization.C450Source14GroupedC04.valid13
#print axioms N11Formalization.C450Source14GroupedC04.valid14
#print axioms N11Formalization.C450Source14GroupedC04.valid15
#print axioms N11Formalization.C450Source14GroupedC04.valid16
#print axioms N11Formalization.C450Source14GroupedC04.valid17
#print axioms N11Formalization.C450Source14GroupedC04.valid18
#print axioms N11Formalization.C450Source14GroupedC04.valid19
#print axioms N11Formalization.C450Source14GroupedC04.valid20
#print axioms N11Formalization.C450Source14GroupedC04.valid21
#print axioms N11Formalization.C450Source14GroupedC04.valid22
#print axioms N11Formalization.C450Source14GroupedC04.valid23
#print axioms N11Formalization.C450Source14GroupedC04.bound
#print axioms N11Formalization.C450Source14GroupedC04.endpoint_checks
