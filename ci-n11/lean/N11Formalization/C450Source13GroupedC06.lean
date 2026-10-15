import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((3232739287:ℚ)/5000000000),((3379028091:ℚ)/5000000000),((-33649309001:ℚ)/49600000000),((-2848739287:ℚ)/5150000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5534410891:ℚ)/10000000000),((227464795699811430670530916808445889865157196054330436339563:ℚ)/4854569763840000000000000000000000000000000000000000000000000),((5475351240971092183166281:ℚ)/23104000000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((167583259:ℚ)/250000000),((3438488739:ℚ)/5000000000),((-34303376129:ℚ)/51500000000),((-148383259:ℚ)/262250000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((981340801:ℚ)/2000000000),((2100717293539151885137478299657422496419204157294149819757849:ℚ)/46970229825273437500000000000000000000000000000000000000000000),((5472361257834279400052121:ℚ)/23104000000000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((272889867:ℚ)/400000000),((3497946333:ℚ)/5000000000),((-34957409663:ℚ)/52450000000),((-80723289:ℚ)/142400000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4563565799:ℚ)/10000000000),((179538136468714335214445383415970124902258585043534778087:ℚ)/4013067881289062500000000000000000000000000000000000000000),((5471286102581910560674889:ℚ)/23104000000000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-11:ℚ)/16),((-5:ℚ)/8),((6941157061:ℚ)/10000000000),((7055348071:ℚ)/10000000000),((-23522942927:ℚ)/35600000000),((-6173157061:ℚ)/10775000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4194571967:ℚ)/10000000000),((5372138420252391010302940800523874396439377789255572966621:ℚ)/122771012258437500000000000000000000000000000000000000000000),((1151537621502552792131739:ℚ)/4864000000000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7000610129:ℚ)/10000000000),((7085075243:ℚ)/10000000000),((-70895827673:ℚ)/107750000000),((-6232610129:ℚ)/10822500000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((3998152801:ℚ)/10000000000),((79270096831217731625495231088807897842535604482260730493382897:ℚ)/1831542659327186279296875000000000000000000000000000000000000000),((1151381864922386173400371:ℚ)/4864000000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((1757584037:ℚ)/2500000000),((1778700517:ℚ)/2500000000),((-1978411743:ℚ)/3006250000),((-1565584037:ℚ)/2717500000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3896443117:ℚ)/10000000000),((46950788585668940318432022681706811149475596180625401851:ℚ)/1084532717992248535156250000000000000000000000000000000000),((1367199991913400101895289:ℚ)/5776000000000000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7060061829:ℚ)/10000000000),((7144528549:ℚ)/10000000000),((-71549814039:ℚ)/108700000000),((-6292061829:ℚ)/10917500000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((3792150493:ℚ)/10000000000),((82861016832879945031298562003376580701169617464517564746196239:ℚ)/1913573052346997421875000000000000000000000000000000000000000000),((21874147855978011371847401:ℚ)/92416000000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((3544893589:ℚ)/5000000000),((7174254693:ℚ)/10000000000),((-6534254693:ℚ)/9925000000),((-185934917:ℚ)/322500000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((460631891:ℚ)/1250000000),((220205584281514968186217686868717209611234029519549681733:ℚ)/5084180827602539062500000000000000000000000000000000000000),((21873099389310827091022249:ℚ)/92416000000000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-11:ℚ)/16),((-5:ℚ)/8),((3559756099:ℚ)/5000000000),((3601990251:ℚ)/5000000000),((-36101892761:ℚ)/54825000000),((-3175756099:ℚ)/5506250000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((3574904637:ℚ)/10000000000),((1731587434177634511940752004930082030181227786933386692618961:ℚ)/39970332364278208007812500000000000000000000000000000000000000),((5468013617589615862545001:ℚ)/23104000000000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((3574618447:ℚ)/5000000000),((3616852991:ℚ)/5000000000),((-36265382901:ℚ)/55062500000),((-3190618447:ℚ)/5530000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((86535171:ℚ)/250000000),((43206722067116407486029118660352159109210229519746903304769:ℚ)/997121496002049446105957031250000000000000000000000000000000),((5467753274713859105308081:ℚ)/23104000000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((717896127:ℚ)/1000000000),((226982223:ℚ)/312500000),((-325257779:ℚ)/493750000),((-213698709:ℚ)/370250000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3344220409:ℚ)/10000000000),((10727532274247414971941744151237165496073591595592246113:ℚ)/247515681628189086914062500000000000000000000000000000000),((170859181832154984884707:ℚ)/722000000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((720868533:ℚ)/1000000000),((7293155969:ℚ)/10000000000),((-73184715659:ℚ)/111075000000),((-644068533:ℚ)/1115500000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3222942457:ℚ)/10000000000),((23100770190511675391380044341596949046709644860393036194068619:ℚ)/532890694664716585693359375000000000000000000000000000000000000),((21868940997113563668250961:ℚ)/92416000000000000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((3619204539:ℚ)/5000000000),((1464576097:ℚ)/2000000000),((-14702337067:ℚ)/22310000000),((-3235204539:ℚ)/5601250000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((3097091791:ℚ)/10000000000),((483387623560991488506405973564946626144066615788503794564843:ℚ)/11148555572032107550000000000000000000000000000000000000000000),((874716410655823310971409:ℚ)/3696640000000000000000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-11:ℚ)/16),((-5:ℚ)/8),((7268132517:ℚ)/10000000000),((459537793:ℚ)/625000000),((-4614915723:ℚ)/7001562500),((-2166710839:ℚ)/3750000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((2966085817:ℚ)/10000000000),((167455875068833362314351179432965857799681069473886187:ℚ)/3861334561200141906738281250000000000000000000000000000),((341670048158979592488521:ℚ)/1444000000000000000000000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7297855653:ℚ)/10000000000),((7412052169:ℚ)/10000000000),((-8276952651:ℚ)/12500000000),((-6529855653:ℚ)/11345000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((565841569:ℚ)/2000000000),((1377610193873705233658560000427580422691378642224613159611:ℚ)/31423101806640625000000000000000000000000000000000000000000),((21866739367942617071726561:ℚ)/92416000000000000000000000)⟩
theorem valid14 : Valid source13 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((1839325257:ℚ)/2500000000),((1494299689:ℚ)/2000000000),((-15029296579:ℚ)/22690000000),((-1647325257:ℚ)/2860000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1266994513:ℚ)/5000000000),((13093900731611208342360751764876243425116341455877971132379:ℚ)/298597093184926250000000000000000000000000000000000000000000),((874588391313217949338721:ℚ)/3696640000000000000000000)⟩
theorem valid15 : Valid source13 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((463546577:ℚ)/625000000),((948798437:ℚ)/1250000000),((-66830649:ℚ)/100000000),((-415546577:ℚ)/726875000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2200454469:ℚ)/10000000000),((75684847387197700410792267057278693811208323286264161:ℚ)/1690711250000000000000000000000000000000000000000000000),((341632703466121205830969:ℚ)/1444000000000000000000000)⟩
theorem valid16 : Valid source13 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((7535630243:ℚ)/10000000000),((770927207:ℚ)/1000000000),((-7776199277:ℚ)/11630000000),((-6767630243:ℚ)/11820000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((260487051:ℚ)/2000000000),((853968146704611469193174525266059728131673308515978200373:ℚ)/19077506851038437500000000000000000000000000000000000000000),((230075637301417973:ℚ)/972800000000000000)⟩
theorem valid17 : Valid source13 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-11:ℚ)/16),((-5:ℚ)/8),((3827255453:ℚ)/5000000000),((7947028623:ℚ)/10000000000),((-80377314853:ℚ)/118200000000),((-3443255453:ℚ)/6100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((1070864398752544592421803415367186493360563443785169717162599:ℚ)/23043230675730000000000000000000000000000000000000000000000000),((30267411:ℚ)/128000000)⟩
theorem valid18 : Valid source13 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((1973065001:ℚ)/2500000000),((8422496527:ℚ)/10000000000),((-85607461797:ℚ)/122000000000),((-1781065001:ℚ)/3240000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((738988171778330049727212467206151440942619888648124881931077:ℚ)/14892223410000000000000000000000000000000000000000000000000000),((30267411:ℚ)/128000000)⟩
theorem valid19 : Valid source13 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((8367714313:ℚ)/10000000000),((2580980789:ℚ)/2500000000),((-26630788679:ℚ)/32400000000),((-7599714313:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((8510474869106891761118673621105397823940282967924498693:ℚ)/127545840000000000000000000000000000000000000000000000000),((30267411:ℚ)/128000000)⟩
theorem valid20 : Valid source13 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((10269099507:ℚ)/10000000000),((7062798563:ℚ)/5000000000),((-74170784193:ℚ)/80000000000),((-3167033169:ℚ)/7360000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1144412705143986487520954132807349000091:ℚ)/13542400000000000000000000000000000000000),((30267411:ℚ)/128000000)⟩
theorem valid21 : Valid source13 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source13 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source13 nn0 nn1 packet21 valid21
private theorem node0_2 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((4329:ℚ)/6400) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source13 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4329:ℚ)/6400) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((4329:ℚ)/6400) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source13 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source13 nn0 nn1 Qcell ((4329:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source13 nn0 nn1 Qcell ((881:ℚ)/1280) ((4443:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source13 nn0 nn1 Qcell ((2193:ℚ)/3200) ((4443:ℚ)/6400) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source13 nn0 nn1 Qcell ((4329:ℚ)/6400) ((4443:ℚ)/6400) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((4443:ℚ)/6400) :=
  cell_join node0_5 node5_11
private theorem node11_13 :
    CellBound source13 nn0 nn1 Qcell ((4443:ℚ)/6400) ((4481:ℚ)/6400) :=
  cell_join leaf11 leaf12
private theorem node14_16 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source13 nn0 nn1 Qcell ((4481:ℚ)/6400) ((143:ℚ)/200) :=
  cell_join leaf13 node14_16
private theorem node11_16 :
    CellBound source13 nn0 nn1 Qcell ((4443:ℚ)/6400) ((143:ℚ)/200) :=
  cell_join node11_13 node13_16
private theorem node17_19 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf16 node17_19
private theorem node20_22 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf20 leaf21
private theorem node19_22 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf19 node20_22
private theorem node16_22 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node16_19 node19_22
private theorem node11_22 :
    CellBound source13 nn0 nn1 Qcell ((4443:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node11_16 node16_22
private theorem node0_22 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_22
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_22
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21]
theorem packet_count : packets.length = 22 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC06
#check @N11Formalization.C450Source13GroupedC06.bound
#print axioms N11Formalization.C450Source13GroupedC06.valid0
#print axioms N11Formalization.C450Source13GroupedC06.valid1
#print axioms N11Formalization.C450Source13GroupedC06.valid2
#print axioms N11Formalization.C450Source13GroupedC06.valid3
#print axioms N11Formalization.C450Source13GroupedC06.valid4
#print axioms N11Formalization.C450Source13GroupedC06.valid5
#print axioms N11Formalization.C450Source13GroupedC06.valid6
#print axioms N11Formalization.C450Source13GroupedC06.valid7
#print axioms N11Formalization.C450Source13GroupedC06.valid8
#print axioms N11Formalization.C450Source13GroupedC06.valid9
#print axioms N11Formalization.C450Source13GroupedC06.valid10
#print axioms N11Formalization.C450Source13GroupedC06.valid11
#print axioms N11Formalization.C450Source13GroupedC06.valid12
#print axioms N11Formalization.C450Source13GroupedC06.valid13
#print axioms N11Formalization.C450Source13GroupedC06.valid14
#print axioms N11Formalization.C450Source13GroupedC06.valid15
#print axioms N11Formalization.C450Source13GroupedC06.valid16
#print axioms N11Formalization.C450Source13GroupedC06.valid17
#print axioms N11Formalization.C450Source13GroupedC06.valid18
#print axioms N11Formalization.C450Source13GroupedC06.valid19
#print axioms N11Formalization.C450Source13GroupedC06.valid20
#print axioms N11Formalization.C450Source13GroupedC06.valid21
#print axioms N11Formalization.C450Source13GroupedC06.bound
#print axioms N11Formalization.C450Source13GroupedC06.endpoint_checks
